use std::{
    collections::hash_map::{HashMap, Entry},
    iter,
    ptr::NonNull,
    rc::Rc,
    borrow::Cow,
};

use rstarc_types::{Value, value_constants::*};
use lang_constructs::LangVariable;
use syntax::ast::Comparator;
use base_analysis::{ScopeId, VariableType};

use codegen::CodegenError;
use codegen::simple_ir::{
    IRProgram,
    SimpleIR,
    IRSubRoutine,
    IRClosure,
    IRFuncParams,
    IRValue,
    IRLValue,
    BinOp,
    InPlaceOp,
    LocalTemp,
    LocalDynTemp,
};
use codegen::closure_layout::ClosureLayout;
use codegen::llvm_api::*;

const MAX_SUPPORTED_ARITY: usize = 5;

// Leave file paths as strings because that's how they're input from the CLI
// and the complexity of interacting between paths and FFI isn't worth it.
pub struct CodegenOptions<'a> {
    pub source_file: &'a str,
    pub llvm_dump: bool,
    pub output: Option<&'a str>,
    pub opt_level: u32,
}

pub fn lower_ir<'a, 'prog: 'a>(program: &'a IRProgram<'prog>, opts: &CodegenOptions)
    -> Result<(), CodegenError>
{
    let mut llh = LLVMHandle::for_native_target(opts.source_file);
    let mut func_decs = HashMap::new();

    // Function declarations
    {
        let llvm_func = llh.add_function(
            "main",
            &mut [],
            int32_type(),
            None,
            None,
        );

        func_decs.insert(0, llvm_func);
    }

    for def in &program.funcs {
        let i64t = int64_type();
        let i8t = int8_type();

        let captures_type = def
            .closure()
            .and_then(|c| build_captured_closure_type(program, c).map(NonNull::as_ptr));

        let mut arg_ts: Vec<_> = iter::once(ptr_type(captures_type.unwrap_or(i8t)))
            .chain(def.func_params.args.iter().map(|_| i64t))
            .collect();

        let llvm_func = llh.add_function(
            &format!("{}", def.func_params.initial_var),
            &mut arg_ts,
            i64t,
            Some(LLVMLinkage::LLVMPrivateLinkage),
            None,
        );

        func_decs.insert(def.scope_id, llvm_func);
    }

    declare_builtin_functions(&mut llh);

    let declarations = Declarations {
        globals: build_global_var_refs(&mut llh, program),
        functions: func_decs,
    };

    // Lower main
    lower_function(&mut llh, program, &declarations, &program.main);

    // Lower other functions
    for func_def in &program.funcs {
        lower_function(&mut llh, program, &declarations, func_def);
    }

    llh.finalize(opts)
}

struct Declarations<'a, 'prog> {
    globals: HashMap<(&'a LangVariable<'prog>, ScopeId), LLVMValueRef>,
    functions: HashMap<ScopeId, FunctionHandle>,
}

/// Declare and initialize global variables
fn build_global_var_refs<'a, 'prog>(llh: &mut LLVMHandle,
                                    program: &'a IRProgram<'prog>)
    -> HashMap<(&'a LangVariable<'prog>, ScopeId), LLVMValueRef>
{
    let i64t = int64_type();
    let initial_value = llh.const_uint(i64t, MYSTERIOUS_BITS);

    let mut globals = HashMap::new();

    for (var, scope) in &program.globals {
        let global_ref = llh.add_global(
            i64t,
            &format!("{}<{}>", var, scope),
            Some(initial_value),
            Some(LLVMLinkage::LLVMPrivateLinkage),
            None,
        );

        globals.insert((var, 0), global_ref);
    }

    globals
}

#[derive(Copy, Clone)]
enum UserFuncDataFields {
    FuncPtr = 0,
    Arity = 1,
    ClosureSize = 2,
    ClosureArgs = 3,
}

impl UserFuncDataFields {
    fn get_ptr(&self, llh: &mut LLVMHandle, value: LLVMValueRef, name: &str)
        -> LLVMValueRef
    {
        let i64t = int64_type();
        let i32t = int32_type();

        llh.build_in_bounds_get_elem_ptr(
            value,
            &mut [llh.const_uint(i64t, 0), llh.const_uint(i32t, *self as u64)],
            name,
        )
    }
}

fn user_func_type(closure_capture_type: Option<NonNull<LLVMType>>) -> LLVMTypeRef {
    let i8t = int8_type();
    let i64t = int64_type();

    struct_type(&mut [
        ptr_type(i8t), // function pointer
        i64t, // arity; should be usize
        i64t, // closure capture size; should be usize
        closure_capture_type.map_or_else(|| struct_type(&mut []), NonNull::as_ptr),
    ])
}

fn declare_builtin_functions(llh: &mut LLVMHandle) {
    let i8t = int8_type();
    let i32t = int32_type();
    let f64t = float64_type();
    let i64t = int64_type();
    let void = void_type();

    llh.declare_builtin_function("llvm.trap", &mut [], void);

    llh.declare_builtin_function("roll_say", &mut [i64t], void);
    llh.declare_builtin_function("roll_alloc", &mut [i64t], ptr_type(i8t));
    llh.declare_builtin_function("roll_mk_number", &mut [f64t], i64t);
    llh.declare_builtin_function("roll_trap_bad_call", &mut [i64t], void);
    llh.declare_builtin_function("roll_coerce_boolean", &mut [i64t], i8t);
    llh.declare_builtin_function("roll_incr", &mut [i64t, i32t], i64t);
    llh.declare_builtin_function("roll_decr", &mut [i64t, i32t], i64t);

    // Binary operations
    let bin_ops = &[
        "roll_is",
        "roll_is_not",
        "roll_gt",
        "roll_lt",
        "roll_ge",
        "roll_le",
        "roll_add",
        "roll_sub",
        "roll_mul",
        "roll_div",
        "roll_and",
        "roll_or",
    ];

    for op in bin_ops {
        llh.declare_builtin_function(op, &mut [i64t, i64t], i64t);
    }
}

fn lower_function<'a, 'prog: 'a, FP>(
    llh: &mut LLVMHandle,
    program: &'a IRProgram<'prog>,
    declarations: &Declarations<'a, 'prog>,
    def: &IRSubRoutine<'prog, FP>,
)
    where
        IRSubRoutine<'prog, FP>: IRClosure<'prog>,
{
    let scope_id = def.scope_id;

    let mut vmgr = ValueTracker::new(program, declarations, def);
    let llvm_func = declarations.functions.get(&scope_id)
        .expect("function by scope");

    // TODO: these initializations should be handled while creating ValueTracker

    // Create entry block
    let entry_block = vmgr.basic_block(llh, "entry".into());
    llh.enter_block(entry_block);

    // Initialize allocas
    for (var, _) in program.scope_map.get_owned_vars_for_scope(scope_id) {
        vmgr.prepare_variable(llh, var, scope_id);
    }
    vmgr.prepare_dyn_temporaries(llh, def.dyn_temp_count);
    vmgr.prepare_closure_locals(llh);
    vmgr.prepare_closure_capture(llh);

    // Translate ops
    for op in &def.ops {
        match op {
            SimpleIR::Jump(label) => {
                let block = vmgr.basic_block(llh, label.name());
                llh.build_br(block);
            }
            SimpleIR::JumpIf(cond, if_label, else_label) => {
                let cond_ref = vmgr.val_to_llvm(llh, cond);

                let coerced_cond_ref = llh.build_call_coerce_boolean(cond_ref, "coerce_bool");
                let truncd_cond_ref = llh.build_trunc(coerced_cond_ref, int1_type(), "trunc_bool");

                let if_bb = vmgr.basic_block(llh, if_label.name());
                let else_bb = vmgr.basic_block(llh, else_label.name());

                llh.build_cond_br(truncd_cond_ref, if_bb, else_bb);
            }
            SimpleIR::Label(label) => {
                let block = vmgr.basic_block(llh, label.name());
                llh.enter_block(block);
            }
            SimpleIR::Operate(bin_op, out, in1, in2) => {
                let builtin = match bin_op {
                    BinOp::Compare(Comparator::Is) => "roll_is",
                    BinOp::Compare(Comparator::IsNot) => "roll_is_not",
                    BinOp::Compare(Comparator::IsGreaterThan) => "roll_gt",
                    BinOp::Compare(Comparator::IsLessThan) => "roll_lt",
                    BinOp::Compare(Comparator::IsAsGreatAs) => "roll_ge",
                    BinOp::Compare(Comparator::IsAsLittleAs) => "roll_le",
                    BinOp::Add => "roll_add",
                    BinOp::Sub => "roll_sub",
                    BinOp::Mul => "roll_mul",
                    BinOp::Div => "roll_div",
                };
                let arg1 = vmgr.val_to_llvm(llh, in1);
                let arg2 = vmgr.val_to_llvm(llh, in2);

                vmgr.store(llh, out, "builtin_out", |llh, name| {
                    llh.build_call_builtin2(builtin, arg1, arg2, name)
                });
            }
            SimpleIR::InPlace(op, ref out) => {
                let (builtin, count) = match *op {
                    InPlaceOp::Incr(count) => ("roll_incr", count),
                    InPlaceOp::Decr(count) => ("roll_decr", count),
                };

                match out {
                    IRLValue::Variable(..) => {}
                    _ => panic!("Unexpected incr/decr target: {:?}", out),
                };

                let in_val = vmgr.val_to_llvm(llh, &out.into());
                let count_val = llh.const_uint(int32_type(), count as u64);

                vmgr.store(llh, out, "inplace_out", |llh, name| {
                    llh.build_call_builtin2(builtin, in_val, count_val, name)
                });
            }
            &SimpleIR::LoadArg(ref out, idx) => {
                let out_ref = vmgr.lval_to_llvm(out)
                    .unwrap_mem(op)
                    .build_ptr(llh, "load-arg");

                // Add 1 to skip the captured closures
                llh.build_store(llvm_func.param(idx + 1), out_ref);
            }
            SimpleIR::Store(out, val) => {
                let out_ref = vmgr.lval_to_llvm(out)
                    .unwrap_mem(op)
                    .build_ptr(llh, "store");

                let val_ref = vmgr.val_to_llvm(llh, val);
                llh.build_store(val_ref, out_ref);
            }
            SimpleIR::Call(out, func, args) => {
                let func_ref = vmgr.val_to_llvm(llh, func);

                let mut arg_refs: Vec<_> = args.iter()
                    .map(|a| vmgr.val_to_llvm(llh, a))
                    .collect();

                vmgr.store(llh, out, &format!("{}.return", func), |llh, name| {
                    build_dynamic_call(
                        llh,
                        &llvm_func,
                        func,
                        func_ref,
                        &mut arg_refs,
                        name,
                    )
                });
            }
            SimpleIR::Say(val) => {
                let arg = vmgr.val_to_llvm(llh, val);
                llh.build_call_say(arg);
            }
            SimpleIR::Return(val) => {
                let arg = vmgr.val_to_llvm(llh, val);
                llh.build_return(arg);
            }
            SimpleIR::ReturnDefault => {
                let retval = if scope_id == 0 {
                    llh.const_uint(int32_type(), 0)
                } else {
                    llh.const_uint(int64_type(), MYSTERIOUS_BITS)
                };

                llh.build_return(retval);
            }
        }
    }
}

fn build_dynamic_call(llh: &mut LLVMHandle,
                      caller_hdl: &FunctionHandle,
                      ir_fn: &IRValue,
                      fn_val: LLVMValueRef,
                      user_args: &mut [LLVMValueRef],
                      return_name: &str)
                      -> LLVMValueRef
{
    let i64t = int64_type();

    // Check that value is a function
    let preheader_block = llh.new_block(caller_hdl, &format!("{}.call.preheader", ir_fn));
    llh.build_br(preheader_block);
    llh.enter_block(preheader_block);

    let fn_masked = llh.build_and(
        fn_val, llh.const_uint(i64t, TAG_MASK), &format!("{}.type", ir_fn)
    );
    let fn_tck = llh.build_icmp(
        LLVMIntEQ,
        fn_masked,
        llh.const_uint(i64t, FUNCTION_TAG),
        &format!("{}.type.check", ir_fn),
    );

    let bad_call_block = {
        let bb = llh.new_block(caller_hdl, &format!("{}.call.bad_type", ir_fn));
        llh.enter_block(bb);

        let trap = llh.builtin_ptr("roll_trap_bad_call");

        llh.build_call(trap, &mut[fn_val], "");
        llh.build_unreachable();

        bb
    };
    let header_block = llh.new_block(caller_hdl, &format!("{}.call.header", ir_fn));

    llh.enter_block(preheader_block);
    llh.build_cond_br(fn_tck, header_block, bad_call_block);

    // Extract the function pointer and arity
    llh.enter_block(header_block);

    let fn_coerced = llh.build_and(
        fn_val,
        llh.const_uint(i64t, !TAG_MASK),
        &format!("{}.coerce", ir_fn),
    );

    let fn_cast = llh.build_int_to_ptr(
        fn_coerced,
        ptr_type(user_func_type(None)),
        &format!("{}.fn_cast", ir_fn),
    );

    let fn_ref_ptr_value = UserFuncDataFields::FuncPtr
        .get_ptr(llh, fn_cast, &format!("{}.fn_ref.ptr", ir_fn));

    let fn_ref_value = llh.build_load(fn_ref_ptr_value, &format!("{}.fn_ref", ir_fn));

    let arity_ptr_value = UserFuncDataFields::Arity
        .get_ptr(llh, fn_cast, &format!("{}.arity.ptr", ir_fn));

    let arity_value = llh.build_load(arity_ptr_value, &format!("{}.arity", ir_fn));

    // Switch over the arity and call the function
    let abort_block = {
        let bb = llh.new_block(caller_hdl, &format!("{}.call.abort", ir_fn));
        llh.enter_block(bb);
        llh.build_trap();
        bb
    };

    llh.enter_block(header_block);

    let captures_ptr_value = UserFuncDataFields::ClosureArgs
        .get_ptr(llh, fn_cast, &format!("{}.captures.ptr", ir_fn));

    let mut args: Vec<_> = iter::once(captures_ptr_value)
        .chain(user_args.iter().copied())
        .collect();

    let switch_inst = llh.build_switch(arity_value, abort_block, MAX_SUPPORTED_ARITY as u32);
    let return_block = llh.new_block(caller_hdl, &format!("{}.call.return", ir_fn));

    let incoming: Vec<_> = (0..=MAX_SUPPORTED_ARITY).map(|user_arg_count| {
        let name = &format!("{}.call.argcount.{}", ir_fn, user_arg_count);

        let (v, bb) = build_call_branch(
            llh, fn_ref_value, &mut args, user_arg_count, return_block, name
        );

        let user_arg_count_ref = llh.const_uint(i64t, user_arg_count as u64);
        llh.add_case(switch_inst, user_arg_count_ref, bb);

        (v, bb)
    }).collect();

    llh.enter_block(return_block);
    llh.build_phi(i64t, &incoming, return_name)
}

fn build_call_branch(llh: &mut LLVMHandle,
                     fnptr_value: LLVMValueRef,
                     args: &mut [LLVMValueRef],
                     user_arg_count: usize,
                     return_block: LLVMBasicBlockRef,
                     name: &str)
                     -> (LLVMValueRef, LLVMBasicBlockRef)
{
    let i64t = int64_type();

    let bb = llh.new_block_before(return_block, name);
    llh.enter_block(bb);

    let arg_count = user_arg_count + 1;

    let mut extended_args;

    let args = if arg_count < args.len() {
        &mut args[..arg_count]
    } else {
        let mysterious_value = llh.const_uint(i64t, MYSTERIOUS_BITS);

        extended_args = args.iter()
            .copied()
            .chain((args.len()..arg_count).map(|_| mysterious_value))
            .collect::<Vec<_>>();

        &mut extended_args
    };

    let mut arg_types: Vec<_> = args.iter()
        .enumerate()
        .map(|(i, _)| if i == 0 { ptr_type(struct_type(&mut [])) } else { i64t })
        .collect();

    let fn_cast = llh.build_bitcast(
        fnptr_value,
        ptr_type(func_type(&mut arg_types, i64t)),
        &format!("{}.cast", name),
    );

    let out_ref = llh.build_call(fn_cast, args, &format!("{}.out", name));

    llh.build_br(return_block);

    (out_ref, bb)
}

#[derive(Debug, Clone)]
enum MemoryTarget {
    Simple(LLVMValueRef),
    ClosureLocal(LLVMValueRef, usize),
    ClosureCapture(LLVMValueRef, usize, usize),
}

impl MemoryTarget {
    fn build_ptr(&self, llh: &mut LLVMHandle, base_name: &str) -> LLVMValueRef {
        match *self {
            MemoryTarget::Simple(mem_ref) => mem_ref,
            MemoryTarget::ClosureLocal(mem_ref, offset) => {
                llh.build_in_bounds_get_elem_ptr(
                    mem_ref,
                    &mut [
                        llh.const_uint(int64_type(), 0),
                        llh.const_uint(int32_type(), offset as u64),
                    ],
                    &format!("{}.closure-var", base_name),
                )
            }
            MemoryTarget::ClosureCapture(mem_ref, capture_offset, value_offset) => {
                let capture_ref = llh.build_in_bounds_get_elem_ptr(
                    mem_ref,
                    &mut [
                        llh.const_uint(int64_type(), 0),
                        llh.const_uint(int32_type(), capture_offset as u64),
                    ],
                    &format!("{}.closure-capture.ptr", base_name),
                );

                let load_ref = llh.build_load(
                    capture_ref, &format!("{}.closure-capture", base_name)
                );

                llh.build_in_bounds_get_elem_ptr(
                    load_ref,
                    &mut [
                        llh.const_uint(int64_type(), 0),
                        llh.const_uint(int32_type(), value_offset as u64),
                    ],
                    &format!("{}.closure-var", base_name),
                )
            }
        }
    }
}

#[derive(Debug, Clone)]
enum LLWriteTarget {
    /// Temporary to be instantiated
    Temp(LocalTemp),
    /// Value ref for an alloca
    Mem(MemoryTarget),
}

impl LLWriteTarget {
    fn unwrap_mem(&self, op: &SimpleIR) -> &MemoryTarget {
        match self {
            LLWriteTarget::Mem(r) => r,
            LLWriteTarget::Temp(t) => {
                panic!("Expected operation {:?} to apply to a memory operand, \
                        but got temporary {}", op, t);
            }
        }
    }
}

/// Handles translation of values for LLVM in a single scope
struct ValueTracker<'a, 'prog: 'a, FP>
where
    IRSubRoutine<'prog, FP>: IRClosure<'prog>,
{
    program: &'a IRProgram<'prog>,
    declarations: &'a Declarations<'a, 'prog>,
    func_hdl: &'a FunctionHandle,
    subroutine: &'a IRSubRoutine<'prog, FP>,

    local_closure_type: Option<NonNull<LLVMType>>,
    local_closure_value: Option<NonNull<LLVMValue>>,

    captured_closure_type: Option<NonNull<LLVMType>>,
    captured_closure_value: Option<NonNull<LLVMValue>>,

    /// Temporary values in trivial SSA form
    static_temps: HashMap<LocalTemp, LLVMValueRef>,
    /// Allocas for local variables
    allocas: HashMap<LangVariable<'prog>, LLVMValueRef>,
    /// Allocas for local dynamic temporaries
    temp_allocas: HashMap<LocalDynTemp, LLVMValueRef>,
    /// A list of basic blocks defined in scope, identified by the name
    /// of an IR label
    /// TODO: Make this key on IR labels directly, and also not require
    /// ownership of a string?!
    basic_blocks: HashMap<String, LLVMBasicBlockRef>,
    /// Cache of strings used in scope
    /// FIXME: This should be program-wide, and should probably be done
    /// in an interning pass when converting to IR
    string_cache: HashMap<Rc<Cow<'prog, str>>, LLVMValueRef>,
}

impl<'a, 'prog: 'a, FP> ValueTracker<'a, 'prog, FP>
where
    IRSubRoutine<'prog, FP>: IRClosure<'prog>,
{
    fn new(program: &'a IRProgram<'prog>,
           declarations: &'a Declarations<'a, 'prog>,
           subroutine: &'a IRSubRoutine<'prog, FP>) -> Self
    {
        let func_hdl = declarations.functions.get(&subroutine.scope_id)
            .expect("ValueTracker own scope func handle");

        ValueTracker {
            program,
            declarations,
            func_hdl,
            subroutine,

            local_closure_type: subroutine.closure()
                .and_then(|closure| build_local_closure_type(closure)),
            local_closure_value: None,

            captured_closure_type: subroutine.closure()
                .and_then(|closure| build_captured_closure_type(program, closure)),
            captured_closure_value: None,

            static_temps: HashMap::new(),
            allocas: HashMap::new(),
            temp_allocas: HashMap::new(),
            basic_blocks: HashMap::new(),
            string_cache: HashMap::new(),
        }
    }

    #[inline]
    fn scope_id(&self) -> ScopeId {
        self.subroutine.scope_id
    }

    fn basic_block(&mut self, llh: &mut LLVMHandle, name: String) -> LLVMBasicBlockRef {
        match self.basic_blocks.entry(name) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let bb = llh.new_block(&self.func_hdl, e.key());
                e.insert(bb);
                bb
            }
        }
    }

    /// Wrapper to handle operations which can take either a variable
    /// or a SimpleIR temporary.
    ///
    /// If they take a variable, a new temporary register has to be
    /// inserted in the LLVM IR, which is then written back to the
    /// variable pointer.
    ///
    /// If they take a temporary, pass the temporary name directly
    /// to the operation.
    ///
    /// TODO: Could just hoist these restrictions to the SimpleIR
    /// level?
    fn store<F>(&mut self,
                llh: &mut LLVMHandle,
                lval: &IRLValue<'prog>,
                fallback_name: &str,
                build: F)
        where F: FnOnce(&mut LLVMHandle, &str) -> LLVMValueRef
    {
        match self.lval_to_llvm(lval) {
            LLWriteTarget::Mem(r) => {
                let src_ref = r.build_ptr(llh, fallback_name);
                let new_temp = build(llh, fallback_name);
                llh.build_store(new_temp, src_ref);
            }
            LLWriteTarget::Temp(t) => {
                let temp_ref = build(llh, &format!("{}", t));
                self.static_temps.insert(t, temp_ref);
            }
        }
    }

    fn lval_to_llvm(&mut self, lval: &IRLValue<'prog>) -> LLWriteTarget {
        match lval {
            IRLValue::Variable(var, var_type, _pos) => {
                LLWriteTarget::Mem(self.get_memory_target(var, var_type))
            }
            IRLValue::LocalTemp(t) => {
                LLWriteTarget::Temp(*t)
            }
            IRLValue::LocalDynTemp(t) => {
                LLWriteTarget::Mem(MemoryTarget::Simple(self.get_temp_memory_variable(*t)))
            }
        }
    }

    /// Translate an IR value to an LLVM representation, emitting instructions
    /// as needed
    fn val_to_llvm(&mut self, llh: &mut LLVMHandle, val: &IRValue<'prog>) -> LLVMValueRef {
        match val {
            IRValue::LocalTemp(temp) => {
                *self.static_temps.get(temp)
                    .unwrap_or_else(|| {
                        panic!("Missing write to temporary {}", temp)
                    })
            }
            IRValue::LocalDynTemp(temp) => {
                let mem_ref = self.get_temp_memory_variable(*temp);
                llh.build_load(mem_ref, &format!("{}.load", temp))
            }
            IRValue::Variable(var, var_type, _pos) => {
                let base_name = format!("{}.load", var);

                let src_ref = self.get_memory_target(var, var_type)
                    .build_ptr(llh, &base_name);

                llh.build_load(src_ref, &base_name)
            }
            IRValue::Literal(Value::Null) => {
                llh.const_uint(int64_type(), NULL_BITS)
            }
            IRValue::Literal(Value::Mysterious) => {
                llh.const_uint(int64_type(), MYSTERIOUS_BITS)
            }
            IRValue::Literal(Value::String(s)) => {
                let global = match self.string_cache.get(s) {
                    Some(g) => Some(*g),
                    None => None,
                };
                let global = global.unwrap_or_else(|| {
                    let g = llh.build_const_string_ptr(s, "string_ptr");
                    self.string_cache.insert(Rc::clone(s), g);
                    g
                });

                tag_pointer(llh, global, CONST_STRING_TAG, "const_str")
            }
            IRValue::Literal(Value::Boolean(b)) => {
                llh.const_uint(int64_type(), if *b { TRUE_BITS } else { FALSE_BITS })
            }
            IRValue::Literal(Value::Number(n)) => {
                let mk = llh.builtin_ptr("roll_mk_number");
                let value = llh.const_float(float64_type(), *n);
                llh.build_call(mk, &mut [value], "num_mk")
            }
            IRValue::Literal(Value::Function(scope_id)) => {
                self.build_function_literal(llh, *scope_id)
            }
        }
    }

    fn build_function_literal(&self, llh: &mut LLVMHandle, scope_id: u64) -> LLVMValueRef {
        let i64t = int64_type();

        let func_params = get_func_params(self.program, scope_id)
            .expect("function literal scope IR meta");

        let closure_capture_type = func_params.closure
            .as_ref()
            .and_then(|c| build_captured_closure_type(self.program, c));

        let func_type = user_func_type(closure_capture_type);

        let alloc = llh.builtin_ptr("roll_alloc");
        let size = llh.build_sizeof(func_type, "sizeof_fn");
        let allocated = llh.build_call(alloc, &mut [size], "fn_alloc");
        let alloc_cast = llh.build_bitcast(allocated, ptr_type(func_type), "fn_alloc.cast");

        {
            let func_ref = self.declarations.functions.get(&scope_id)
                .expect("function literal scope")
                .func_ref();

            let func_ref_cast = llh.build_bitcast(
                func_ref, ptr_type(int8_type()), "fn_ref.cast"
            );

            let func_ref_dest = UserFuncDataFields::FuncPtr
                .get_ptr(llh, alloc_cast, "fn_ref.dest");

            llh.build_store(func_ref_cast, func_ref_dest);
        }

        {
            let arity_dest = UserFuncDataFields::Arity
                .get_ptr(llh, alloc_cast, "arity.dest");

            llh.build_store(llh.const_uint(i64t, func_params.args.len() as u64),
                            arity_dest);
        }

        if let Some(ref closure) = func_params.closure {
            let captures_size_dest = UserFuncDataFields::ClosureSize
                .get_ptr(llh, alloc_cast, "captures_size.dest");

            llh.build_store(
                llh.const_uint(int64_type(), closure.captures().len() as u64),
                captures_size_dest,
            );

            let captures_dest = UserFuncDataFields::ClosureArgs
                .get_ptr(llh, alloc_cast, "captures.dest");

            for capture_scope in closure.captures() {
                let capture_src = if capture_scope == self.scope_id() {
                    self.local_closure_value
                        .expect("locals closure src")
                        .as_ptr()
                } else {
                    let src_offset = self.subroutine.closure()
                        .expect("parent closure")
                        .get_capture_block_offset(capture_scope);

                    let src_capture_closure_value = self.captured_closure_value
                        .expect("parent capture type")
                        .as_ptr();

                    let src_capture_ptr = llh.build_in_bounds_get_elem_ptr(
                        src_capture_closure_value,
                        &mut [
                            llh.const_uint(int64_type(), 0),
                            llh.const_uint(int32_type(), src_offset as u64),
                        ],
                        &format!("captures<{}>.src.ptr", capture_scope),
                    );

                    llh.build_load(src_capture_ptr, &format!("captures<{}>.src", capture_scope))
                };

                let dest_offset = closure.get_capture_block_offset(capture_scope);

                let capture_dest = llh.build_in_bounds_get_elem_ptr(
                    captures_dest,
                    &mut [
                        llh.const_uint(int64_type(), 0),
                        llh.const_uint(int32_type(), dest_offset as u64),
                    ],
                    &format!("captures<{}>.dest", capture_scope),
                );

                llh.build_store(capture_src, capture_dest);
            }
        }

        tag_pointer(llh, alloc_cast, FUNCTION_TAG, "fn_alloc.usr")
    }

    fn prepare_variable(&mut self,
                        llh: &mut LLVMHandle,
                        var: &LangVariable<'prog>,
                        scope_id: ScopeId)
    {
        assert_eq!(self.scope_id(), scope_id,
                   "Variable initialization request for non-local variable");

        let var_type = self.program.scope_map
            .get_variable_type(var, scope_id)
            .expect("variable type scope map lookup");

        match var_type {
            VariableType::Closure(_) | VariableType::Global => {
                // Already addressed
            }
            VariableType::Local(_) => {
                let alloca = llh.build_alloca(int64_type(), &format!("{}", &var));
                self.allocas.insert(*var, alloca);
            }
        }
    }

    fn prepare_dyn_temporaries(&mut self, llh: &mut LLVMHandle, count: u64) {
        let value_t = int64_type();

        (0..count).into_iter()
            .map(|i| LocalDynTemp::new(i))
            .map(|tmp| (tmp, llh.build_alloca(value_t, &format!("{}", tmp))))
            .for_each(|(k, v)| { self.temp_allocas.insert(k, v); });
    }

    fn prepare_closure_locals(&mut self, llh: &mut LLVMHandle) {
        let closure_type = match self.local_closure_type {
            Some(t) => t.as_ptr(),
            None => return,
        };

        let base_name = format!("closure.locals<{}>", self.scope_id());

        let alloc_fn = llh.builtin_ptr("roll_alloc");
        let size = llh.build_sizeof(closure_type, &format!("{}.sizeof", base_name));
        let allocated = llh.build_call(alloc_fn, &mut [size], &format!("{}.alloc", base_name));

        let closure_value = llh.build_bitcast(allocated, ptr_type(closure_type), &base_name);

        self.local_closure_value = Some(NonNull::new(closure_value).expect("closure value"));
    }

    fn prepare_closure_capture(&mut self, llh: &mut LLVMHandle) {
        let closure_type = match self.captured_closure_type {
            Some(t) => t.as_ptr(),
            None => return,
        };

        let alloca = llh.build_alloca(closure_type, "closure_captures");
        let load = llh.build_load(self.func_hdl.param(0), "closure_captures.load");
        llh.build_store(load, alloca);

        self.captured_closure_value = Some(NonNull::new(alloca).expect("capture alloca"));
    }

    fn get_memory_target(&mut self, var: &LangVariable<'prog>, var_type: &VariableType)
        -> MemoryTarget
    {
        match *var_type {
            VariableType::Closure(scope_id) if scope_id == self.scope_id() => {
                let mem_ref = self.local_closure_value.expect("local closure").as_ptr();
                let offset = self.subroutine.closure()
                    .expect("closure offsets for requested variable")
                    .get_local_offset(var);

                MemoryTarget::ClosureLocal(mem_ref, offset)
            }
            VariableType::Closure(scope_id) => {
                let mem_ref = self.captured_closure_value.expect("capture closure").as_ptr();
                let (capture_offset, var_offset) = self.subroutine.closure()
                    .expect("closure offsets for requested variable")
                    .get_capture_offset(scope_id, var);

                MemoryTarget::ClosureCapture(mem_ref, capture_offset, var_offset)
            }
            VariableType::Global => {
                let val = *self.declarations.globals.get(&(var, 0))
                    .expect("global variable lookup");

                MemoryTarget::Simple(val)
            }
            VariableType::Local(scope_id) => {
                assert_eq!(scope_id, self.scope_id(),
                           "unexpected local variable (for var {} in scope {} \
                            from scope {})", var, scope_id, self.scope_id());

                let val = *self.allocas.get(var).unwrap_or_else(|| {
                    panic!("read of {} alloca should follow write", var);
                });

                MemoryTarget::Simple(val)
            }
        }
    }

    fn get_temp_memory_variable(&mut self, temp: LocalDynTemp) -> LLVMValueRef {
        *self.temp_allocas.get(&temp).unwrap_or_else(|| {
            panic!("read of {} alloca should follow write", temp);
        })
    }
}

fn tag_pointer(llh: &mut LLVMHandle,
               ptr_ref: LLVMValueRef,
               tag: u64,
               kind: &str)
               -> LLVMValueRef
{
    let i64t = int64_type();
    let scalar_ref = llh.build_ptr_to_int(ptr_ref,
                                          i64t,
                                          &format!("{}.scalar", kind));

    let func_tag = llh.const_uint(i64t, tag);
    llh.build_xor(scalar_ref, func_tag, &format!("{}.tagged", kind))
}

fn build_local_closure_type(closure: &ClosureLayout) -> Option<NonNull<LLVMType>> {
    let locals_count = closure.locals().len();

    if locals_count == 0 {
        None
    } else {
        Some(NonNull::new(array_type(int64_type(), locals_count as u32))
            .expect("local closure type construction"))
    }
}

fn build_captured_closure_type(program: &IRProgram, closure: &ClosureLayout)
    -> Option<NonNull<LLVMType>>
{
    let mut fields = closure.captures().map(|indirect_scope| {
        let antecedent = get_func_params(program, indirect_scope)
            .expect("closure antecedent params")
            .closure
            .as_ref()
            .expect("closure antecedent closure");

        ptr_type(build_local_closure_type(antecedent)
            .expect("captured closure antecedent")
            .as_ptr())
    }).collect::<Vec<_>>();

    if fields.is_empty() {
        None
    } else {
        Some(NonNull::new(struct_type(&mut fields))
            .expect("closure type construction"))
    }
}

fn get_func_params<'a, 'prog>(program: &'a IRProgram<'prog>, scope_id: ScopeId)
    -> Option<&'a IRFuncParams<'prog>>
{
    // find IR metadata
    // TODO: handle this in O(1)
    let mut func_params = None;
    for ir_func in &program.funcs {
        if ir_func.scope_id == scope_id {
            func_params = Some(&ir_func.func_params);
            break;
        }
    }
    func_params
}

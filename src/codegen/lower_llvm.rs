use std::collections::hash_map::{HashMap, Entry};

use rstarc_types::{Value, value_constants::*};
use lang_constructs::LangVariable;
use syntax::ast::Comparator;
use base_analysis::{ScopeId, VariableType};

use codegen::CodegenError;
use codegen::simple_ir::{IRProgram, SimpleIR, IRFunc, IRBody, IRValue,
                         IRLValue, BinOp, InPlaceOp, LocalTemp, LocalDynTemp};
use codegen::llvm_api::*;

// Leave file paths as strings because that's how they're input from the CLI
// and the complexity of interacting between paths and FFI isn't worth it.
pub struct CodegenOptions<'a> {
    pub source_file: &'a str,
    pub llvm_dump: bool,
    pub output: Option<&'a str>,
    pub opt_level: u32,
}

pub fn lower_ir(program: &IRProgram, opts: &CodegenOptions)
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

        func_decs.insert(0, FunctionTarget {
            direct_func: llvm_func,
            shim_func: None,
        });
    }

    for (func_def, _) in &program.funcs {
        let i64t = int64_type();
        let mut arg_ts: Vec<_> = func_def.args.iter().map(|_| i64t).collect();

        let mut llvm_func = llh.add_function(
            &format!("{}", func_def.initial_var),
            &mut arg_ts,
            i64t,
            Some(LLVMLinkage::LLVMPrivateLinkage),
            None,
        );

        let mut shim_func = build_shim_function(&mut llh, func_def, &llvm_func);

        func_decs.insert(func_def.scope_id, FunctionTarget {
            direct_func: llvm_func,
            shim_func: Some(shim_func),
        });
    }

    declare_builtin_functions(&mut llh);

    let declarations = Declarations {
        globals: build_global_var_refs(&mut llh, program),
        functions: func_decs,
    };

    // Lower main
    lower_function(&mut llh,
                   program,
                   &declarations,
                   0,
                   &program.main,
                   true);

    // Lower other functions
    for (func_def, func_body) in &program.funcs {
        lower_function(&mut llh,
                       program,
                       &declarations,
                       func_def.scope_id,
                       func_body,
                       false);
    }

    llh.finalize(opts)
}

struct Declarations<'a> {
    globals: HashMap<(&'a LangVariable<'a>, ScopeId), LLVMValueRef>,
    functions: HashMap<ScopeId, FunctionTarget>,
}

struct FunctionTarget {
    direct_func: FunctionHandle,
    shim_func: Option<FunctionHandle>,
}

/// Declare and initialize global variables
fn build_global_var_refs<'a>(llh: &mut LLVMHandle,
                             program: &'a IRProgram<'a>)
    -> HashMap<(&'a LangVariable<'a>, ScopeId), LLVMValueRef>
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

/// Build a shim function to normalize function arguments before passing them
/// to the real function.
///
/// The way this is done is by passing the argument count as the first
/// argument to the shim function, which then switches over it and passes
/// the correct number of arguments to the underlying function.
///
/// I don't really know how safe this is in general, and it may come back
/// to haunt me! Offhand, this seems to work (for 64-bit programs, on MacOS,
/// at least). It could break for calling conventions that put more
/// responsibility on the callee.
pub fn build_shim_function(llh: &mut LLVMHandle,
                           func_def: &IRFunc,
                           func_hdl: &FunctionHandle)
                           -> FunctionHandle
{
    let arity = func_def.args.len();
    let i64t = int64_type();

    let mut arg_ts: Vec<_> = (0..arity + 1).map(|_| i64t).collect();
    let shim_hdl = llh.add_function(
        &format!("{}.shim", &format!("{}", func_def.initial_var)),
        &mut arg_ts,
        i64t,
        Some(LLVMLinkage::LLVMPrivateLinkage),
        Some(8),
    );

    let mut args: Vec<_> = (0..arity).map(|i| shim_hdl.param(i + 1)).collect();

    let entry = llh.new_block(&shim_hdl, "entry");
    let full_bb = build_shim_branch(llh, &shim_hdl, func_hdl, &mut args, arity);

    llh.enter_block(entry);

    let switch_inst = llh.build_switch(shim_hdl.param(0), full_bb, arity as u32);
    let mysterious_value = llh.const_uint(i64t, MYSTERIOUS_BITS);

    for missing_count in 1..=arity {
        let arg_count = arity - missing_count;
        args[arg_count] = mysterious_value;

        let branch = build_shim_branch(llh, &shim_hdl, func_hdl, &mut args, arg_count);
        let arg_count_ref = llh.const_uint(i64t, arg_count as u64);
        llh.add_case(switch_inst, arg_count_ref, branch);
    }

    shim_hdl
}

fn build_shim_branch(llh: &mut LLVMHandle,
                     shim_hdl: &FunctionHandle,
                     direct_hdl: &FunctionHandle,
                     args: &mut [LLVMValueRef],
                     arg_count: usize)
                     -> LLVMBasicBlockRef
{
    let bb = llh.new_block(shim_hdl, &format!("argcount.{}", arg_count));
    llh.enter_block(bb);

    let out_ref = llh.build_call(
        direct_hdl.func_ref(),
        args,
        &format!("argcount.{}.out", arg_count),
    );

    llh.build_return(out_ref);
    bb
}

fn declare_builtin_functions(llh: &mut LLVMHandle) {
    let i8t = int8_type();
    let i32t = int32_type();
    let f64t = float64_type();
    let i64t = int64_type();
    let void = void_type();

    llh.declare_builtin_function("roll_say", &mut [i64t], void);
    llh.declare_builtin_function("roll_alloc", &mut [i64t], ptr_type(i64t));
    llh.declare_builtin_function("roll_mk_number", &mut [f64t], i64t);
    llh.declare_builtin_function("roll_coerce_function", &mut [i64t], i64t);
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

fn lower_function(llh: &mut LLVMHandle,
                  program: &IRProgram,
                  declarations: &Declarations,
                  scope_id: ScopeId,
                  body: &IRBody,
                  is_main: bool)
{
    let mut vmgr = ValueTracker::new(program, declarations, scope_id);
    let llvm_func = declarations.functions.get(&scope_id)
        .expect("function by scope")
        .direct_func;

    // Create entry block
    let entry_block = vmgr.basic_block(llh, "entry".into());
    llh.enter_block(entry_block);

    // Initialize allocas
    for (var, _) in program.scope_map.get_owned_vars_for_scope(scope_id) {
        vmgr.prepare_variable(llh, var, scope_id);
    }
    vmgr.prepare_dyn_temporaries(llh, body.dyn_temp_count);

    // Translate ops
    for op in &body.ops {
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
            SimpleIR::InPlace(op, out) => {
                let (builtin, count) = match *op {
                    InPlaceOp::Incr(count) => ("roll_incr", count),
                    InPlaceOp::Decr(count) => ("roll_decr", count),
                };

                match out {
                    IRLValue::Variable(..) => {}
                    _ => panic!("Unexpected incr/decr target: {:?}", out),
                };

                let in_val = vmgr.val_to_llvm(llh, &out.clone().into());
                let count_val = llh.const_uint(int32_type(), count as u64);

                vmgr.store(llh, out, "inplace_out", |llh, name| {
                    llh.build_call_builtin2(builtin, in_val, count_val, name)
                });
            }
            SimpleIR::LoadArg(out, idx) => {
                let out_ref = vmgr.lval_to_llvm(out).unwrap_mem(op);
                llh.build_store(llvm_func.param(*idx), out_ref);
            }
            SimpleIR::Store(out, val) => {
                let out_ref = vmgr.lval_to_llvm(out).unwrap_mem(op);
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
                let retval = if is_main {
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
                      ir_fn: &IRValue,
                      fn_val: LLVMValueRef,
                      args: &mut [LLVMValueRef],
                      name: &str)
                      -> LLVMValueRef
{
    let i64t = int64_type();

    let fn_coerced = llh.build_call_coerce_function(
        fn_val,
        &format!("{}.coerce", ir_fn),
    );

    let arg_count = args.len();
    let arg_count_ref = llh.const_uint(int64_type(), arg_count as u64);

    let mut shim_args = Vec::with_capacity(arg_count + 1);
    shim_args.push(arg_count_ref);
    shim_args.extend(args.iter());

    let mut shim_arg_types: Vec<_> = shim_args.iter().map(|_| i64t).collect();
    let fn_type = ptr_type(func_type(&mut shim_arg_types, i64t));

    let fn_cast = llh.build_int_to_ptr(fn_coerced,
                                       fn_type,
                                       &format!("{}.fn_cast", ir_fn));

    llh.build_call(fn_cast, &mut shim_args, name)
}

#[derive(Debug, Clone, Copy)]
enum LLWriteTarget {
    /// Temporary to be instantiated
    Temp(LocalTemp),
    /// Value ref for an alloca
    Mem(LLVMValueRef),
}

impl LLWriteTarget {
    fn unwrap_mem(&self, op: &SimpleIR) -> LLVMValueRef {
        match self {
            LLWriteTarget::Mem(r) => *r,
            LLWriteTarget::Temp(t) => {
                panic!("Expected operation {:?} to apply to a memory operand, \
                        but got temporary {}", op, t);
            }
        }
    }
}

/// Handles translation of values for LLVM in a single scope
struct ValueTracker<'a> {
    program: &'a IRProgram<'a>,
    declarations: &'a Declarations<'a>,
    func_target: &'a FunctionTarget,
    scope_id: ScopeId,

    /// Temporary values in trivial SSA form
    static_temps: HashMap<LocalTemp, LLVMValueRef>,
    /// Allocas for local variables
    allocas: HashMap<LangVariable<'a>, LLVMValueRef>,
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
    string_cache: HashMap<String, LLVMValueRef>,
}

impl<'a> ValueTracker<'a> {
    fn new(program: &'a IRProgram,
           declarations: &'a Declarations<'a>,
           scope_id: ScopeId) -> Self
    {
        let func_target = declarations.functions.get(&scope_id)
            .expect("ValueTracker own scope func handle");

        ValueTracker {
            program,
            declarations,
            func_target,
            scope_id,

            static_temps: HashMap::new(),
            allocas: HashMap::new(),
            temp_allocas: HashMap::new(),
            basic_blocks: HashMap::new(),
            string_cache: HashMap::new(),
        }
    }

    fn basic_block(&mut self, llh: &mut LLVMHandle, name: String) -> LLVMBasicBlockRef {
        match self.basic_blocks.entry(name) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let func_handle = self.func_target.direct_func;
                let bb = llh.new_block(&func_handle, e.key());
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
                lval: &IRLValue<'a>,
                fallback_name: &str,
                build: F)
        where F: FnOnce(&mut LLVMHandle, &str) -> LLVMValueRef
    {
        match self.lval_to_llvm(lval) {
            LLWriteTarget::Mem(r) => {
                let new_temp = build(llh, fallback_name);
                llh.build_store(new_temp, r);
            }
            LLWriteTarget::Temp(t) => {
                let temp_ref = build(llh, &format!("{}", t));
                self.static_temps.insert(t, temp_ref);
            }
        }
    }

    fn lval_to_llvm(&mut self, lval: &IRLValue<'a>) -> LLWriteTarget {
        match lval {
            IRLValue::Variable(v, i, _pos) => {
                LLWriteTarget::Mem(self.get_memory_variable(v, *i))
            }
            IRLValue::LocalTemp(t) => {
                LLWriteTarget::Temp(*t)
            }
            IRLValue::LocalDynTemp(t) => {
                LLWriteTarget::Mem(self.get_temp_memory_variable(*t))
            }
        }
    }

    /// Translate an IR value to an LLVM representation, emitting instructions
    /// as needed
    fn val_to_llvm(&mut self, llh: &mut LLVMHandle, val: &IRValue<'a>) -> LLVMValueRef {
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
            IRValue::Variable(var, scope_id, _pos) => {
                let mem_ref = self.get_memory_variable(var, *scope_id);
                llh.build_load(mem_ref, &format!("{}.load", var))
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
                    self.string_cache.insert(s.to_string(), g);
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
                let func_ref = self.declarations.functions.get(scope_id)
                    .expect("function literal scope")
                    .shim_func
                    .expect("user-called function")
                    .func_ref();

                tag_pointer(llh, func_ref, FUNCTION_TAG, "func")
            }
        }
    }

    fn prepare_variable(&mut self,
                        llh: &mut LLVMHandle,
                        var: &LangVariable<'a>,
                        scope_id: ScopeId)
    {
        assert_eq!(self.scope_id, scope_id,
                   "Variable initialization request for non-local variable");

        let var_type = self.program.scope_map
            .get_variable_type(var, scope_id);

        match var_type {
            None | Some(VariableType::Closure(_)) => {
                unreachable!("Variable type {:?}", var_type);
            }
            Some(VariableType::Global) => {
                // Already addressed
            },
            Some(VariableType::Local(_)) => {
                let alloca = llh.build_alloca(int64_type(), &format!("{}", &var));
                self.allocas.insert(var.clone(), alloca);
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

    fn get_memory_variable(&mut self, var: &LangVariable<'a>, scope_id: ScopeId)
        -> LLVMValueRef
    {
        if let Some(mem_ref) = self.declarations.globals.get(&(var, scope_id)) {
            return *mem_ref;
        }

        assert!(scope_id == self.scope_id,
                "non-local alloca (for var {} in scope {} from scope {})",
                var,
                scope_id,
                self.scope_id);

        *self.allocas.get(var).unwrap_or_else(|| {
            panic!("read of {} alloca should follow write", var);
        })
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

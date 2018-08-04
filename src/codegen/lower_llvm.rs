use std::collections::hash_map::{HashMap, Entry};

use lang_constructs::{LangVariable, Value};
use ast::Comparator;
use base_analysis::ScopeId;

use codegen::CodegenError;
use codegen::simple_ir::{IRProgram, SimpleIR, IRValue, IRLValue, BinOp,
                         JumpType, LocalTemp};
use codegen::llvm_api::*;

// TODO: Find a way to share these with the runtime
const NULL_BITS: u64 = 0x0;
const FALSE_BITS: u64 = 0x2;
const TRUE_BITS: u64 = 0xa;
const MYSTERIOUS_BITS: u64 = 0x12;
const CONST_STRING_TAG: u64 = 0x3;

// Leave file paths as strings because that's how they're input from the CLI
// and the complexity of interacting between paths and FFI isn't worth it.
pub struct CodegenOptions<'a> {
    pub source_file: &'a str,
    pub llvm_dump: bool,
    pub output: Option<&'a str>,
    pub opt_level: i32,
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
        );

        func_decs.insert(0, llvm_func);
    }

    for (func_def, _) in &program.funcs {
        let i64t = int64_type();
        let mut arg_ts: Vec<_> = func_def.args.iter().map(|_| i64t).collect();

        let mut llvm_func = llh.add_function(
            &format!("{}", func_def.initial_var),
            &mut arg_ts,
            i64t,
        );

        func_decs.insert(func_def.scope_id, llvm_func);
    }

    declare_builtin_functions(&mut llh);

    // Lower main
    lower_function(&mut llh,
                   program,
                   &func_decs,
                   0,
                   &program.main,
                   true);

    // Lower other functions
    for (func_def, func_body) in &program.funcs {
        lower_function(&mut llh,
                       program,
                       &func_decs,
                       func_def.scope_id,
                       func_body,
                       false);
    }

    llh.finalize(opts)
}

fn declare_builtin_functions(llh: &mut LLVMHandle) {
    let f64t = float64_type();
    let i64t = int64_type();
    let void = void_type();

    llh.declare_builtin_function("roll_say", &mut [i64t], void);
    llh.declare_builtin_function("roll_alloc", &mut [i64t], ptr_type(i64t));
    llh.declare_builtin_function("roll_mk_number", &mut [f64t], i64t);

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
                  func_decs: &HashMap<ScopeId, FunctionHandle>,
                  scope_id: ScopeId,
                  body: &[SimpleIR],
                  is_main: bool)
{
    let mut vmgr = ValueTracker::new(func_decs, scope_id);
    let llvm_func = func_decs.get(&scope_id).expect("function by scope");

    // Create entry block
    let entry_block = vmgr.basic_block(llh, "entry".into());
    llh.enter_block(entry_block);

    // Initialize allocas
    for var in program.scope_map.get_owned_vars_for_scope(scope_id) {
        vmgr.build_alloca(llh, var.clone(), scope_id);
    }

    // Translate ops
    let mut last_was_return = false;
    let mut prec_was_br = false;

    for op in body {
        last_was_return = false;

        let mut is_br = false;

        match op {
            SimpleIR::Jump(label) => {
                let block = vmgr.basic_block(llh, label.name());
                llh.build_br(block);

                is_br = true;
            }
            SimpleIR::JumpIf(label, jump_type, val) => {
                // TODO: The simple IR can generate the alt branch
                let label_name = label.name();
                let alt_label_name = format!("{}.alt", &label_name);

                let val_ref = vmgr.val_to_llvm(llh, val);

                // XXX: Assume that the value is a bool. I think the
                // parser forces this to be true at the moment. Probably
                // better to make this stuff conditional and let LLVM
                // prove it though.
                let tag_bytes = llh.const_uint(int64_type(), 3);
                let coerced_val_ref = llh.build_lshr(
                    val_ref,
                    tag_bytes,
                    "coerce_bool",
                );
                let truncd_val_ref = llh.build_trunc(coerced_val_ref, int1_type(), "trunc_bool");

                let (named_bb, alt_bb);

                if let JumpType::If = jump_type {
                    named_bb = vmgr.basic_block(llh, label_name);
                    alt_bb = llh.new_block(llvm_func, &alt_label_name);

                    llh.build_cond_br(truncd_val_ref, named_bb, alt_bb);
                } else {
                    alt_bb = llh.new_block(llvm_func, &alt_label_name);
                    named_bb = vmgr.basic_block(llh, label_name);

                    llh.build_cond_br(truncd_val_ref, alt_bb, named_bb);
                }

                llh.enter_block(alt_bb);
            }
            SimpleIR::Label(label) => {
                let block = vmgr.basic_block(llh, label.name());

                // LLVM really doesn't like redundant branches
                if !prec_was_br {
                    llh.build_br(block);
                }

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
                    BinOp::And => "roll_and",
                    BinOp::Or => "roll_or",
                };
                let arg1 = vmgr.val_to_llvm(llh, in1);
                let arg2 = vmgr.val_to_llvm(llh, in2);

                vmgr.store(llh, out, "builtin_out", |llh, name| {
                    llh.build_call_builtin2(builtin, arg1, arg2, name)
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
                    llh.build_call_dynamic(
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

                last_was_return = true;
            }
        }

        prec_was_br = is_br;
    }

    if !last_was_return {
        let retval;
        if is_main {
            retval = llh.const_uint(int32_type(), 0);
        } else {
            retval = llh.const_uint(int64_type(), MYSTERIOUS_BITS);
        }
        llh.build_return(retval);
    }
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

struct ValueTracker<'a> {
    func_handle: &'a FunctionHandle,
    func_decs: &'a HashMap<ScopeId, FunctionHandle>,
    #[allow(unused)] scope_id: ScopeId,

    temps: HashMap<LocalTemp, LLVMValueRef>,
    allocas: HashMap<LangVariable<'a>, LLVMValueRef>,
    basic_blocks: HashMap<String, LLVMBasicBlockRef>,
    string_cache: HashMap<String, LLVMValueRef>,
}

impl<'a> ValueTracker<'a> {
    fn new(func_decs: &'a HashMap<ScopeId, FunctionHandle>,
           scope_id: ScopeId) -> Self
    {
        let func_handle = func_decs.get(&scope_id)
            .expect("ValueTracker own scope func handle");

        ValueTracker {
            func_handle,
            func_decs,
            scope_id,

            temps: HashMap::new(),
            allocas: HashMap::new(),
            basic_blocks: HashMap::new(),
            string_cache: HashMap::new(),
        }
    }

    fn basic_block(&mut self, llh: &mut LLVMHandle, name: String) -> LLVMBasicBlockRef {
        match self.basic_blocks.entry(name) {
            Entry::Occupied(e) => *e.get(),
            Entry::Vacant(e) => {
                let func_handle = self.func_handle;
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
                self.temps.insert(t, temp_ref);
            }
        }
    }

    fn lval_to_llvm(&mut self, lval: &IRLValue<'a>) -> LLWriteTarget {
        match lval {
            IRLValue::Variable(v, i) => {
                // XXX: Make read_alloca take lang_variable
                LLWriteTarget::Mem(self.read_alloca(v, *i))
            }
            IRLValue::LocalTemp(t) => {
                LLWriteTarget::Temp(*t)
            }
        }
    }

    /// Translate an IR value to an LLVM representation, emitting instructions
    /// as needed
    fn val_to_llvm(&mut self, llh: &mut LLVMHandle, val: &IRValue<'a>) -> LLVMValueRef {
        match val {
            IRValue::LocalTemp(temp) => {
                *self.temps.get(temp)
                    .unwrap_or_else(|| {
                        panic!("Missing write to temporary {}", temp)
                    })
            }
            IRValue::Variable(var, scope_id) => {
                let alloca = self.read_alloca(var, *scope_id);
                llh.build_load(alloca, &format!("{}.load", var))
            }
            IRValue::Literal(Value::Null) => {
                llh.const_uint(int64_type(), NULL_BITS)
            }
            IRValue::Literal(Value::Mysterious) => {
                llh.const_uint(int64_type(), MYSTERIOUS_BITS)
            }
            IRValue::Literal(Value::String(s)) => {
                let i64t = int64_type();

                let global = match self.string_cache.get(s) {
                    Some(g) => Some(*g),
                    None => None,
                };
                let global = global.unwrap_or_else(|| {
                    let g = llh.build_const_string_ptr(s, "string_ptr");
                    self.string_cache.insert(s.to_string(), g);
                    g
                });

                let global_int = llh.build_ptr_to_int(global, i64t, "scalar");

                let const_str_tag = llh.const_uint(i64t, CONST_STRING_TAG);

                llh.build_xor(global_int, const_str_tag, "const_string")
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
                let func_ref = self.func_decs.get(scope_id)
                    .expect("function literal scope")
                    .func_ref();

                llh.build_ptr_to_int(func_ref, int64_type(), "func_scalar")
            }
        }
    }

    fn build_alloca(&mut self,
                    llh: &mut LLVMHandle,
                    var: LangVariable<'a>,
                    scope_id: ScopeId)
        -> LLVMValueRef
    {
        assert_eq!(self.scope_id, scope_id,
                   "Alloca request for non-local variable");

        let alloca = llh.build_alloca(int64_type(), &format!("{}", &var));
        self.allocas.insert(var, alloca);
        alloca
    }

    fn read_alloca(&mut self, var: &LangVariable<'a>, scope_id: ScopeId) -> LLVMValueRef {
        if scope_id != self.scope_id {
            unimplemented!("non-local reads (read for scope {} from scope {})",
                           scope_id,
                           self.scope_id);
        }

        *self.allocas.get(var).unwrap_or_else(|| {
            panic!("read of {} alloca should follow write", var);
        })
    }
}

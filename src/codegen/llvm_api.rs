#![allow(unused)]

use llvm::core::*;
use llvm::prelude::*;
use llvm::target::*;
use llvm::target_machine::*;
use llvm::{LLVMModule, LLVMBuilder};
// Reexports
pub use llvm::LLVMLinkage;
pub use llvm::prelude::{LLVMTypeRef, LLVMValueRef, LLVMBasicBlockRef};

use std::collections::hash_map::{HashMap, Entry};
use std::marker::PhantomData;
use std::ffi::{CStr, CString};

use codegen::CodegenError;

const DEFAULT_ADDRESS_SPACE: u32 = 0;

pub fn dump_value(value_ref: LLVMValueRef) {
    unsafe {
        LLVMDumpValue(value_ref);
    }
    eprintln!("");
}

pub fn void_type() -> LLVMTypeRef {
    unsafe { LLVMVoidType() }
}

pub fn int1_type() -> LLVMTypeRef {
    unsafe { LLVMInt1Type() }
}

pub fn int8_type() -> LLVMTypeRef {
    unsafe { LLVMInt8Type() }
}

pub fn int32_type() -> LLVMTypeRef {
    unsafe { LLVMInt32Type() }
}

pub fn int64_type() -> LLVMTypeRef {
    unsafe { LLVMInt64Type() }
}

pub fn float64_type() -> LLVMTypeRef {
    unsafe { LLVMDoubleType() }
}

pub fn ptr_type(t: LLVMTypeRef) -> LLVMTypeRef {
    unsafe { LLVMPointerType(t, DEFAULT_ADDRESS_SPACE) }
}

pub fn func_type(args: &mut [LLVMTypeRef], ret: LLVMTypeRef) -> LLVMTypeRef {
    let is_vararg = 0;
    unsafe {
        LLVMFunctionType(ret, args.as_mut_ptr(), args.len() as _, is_vararg)
    }
}

/// Handle to an LLVM builder. This implementation is hardcoded to work on a
/// single LLVM module.
pub struct LLVMHandle {
    builder: *mut LLVMBuilder,
    module: *mut LLVMModule,
    target_triple: LLVMString,
    cpu_name: LLVMString,
    cpu_features: LLVMString,
    owned_strings: Vec<CString>,
    builtins: HashMap<&'static str, LLVMValueRef>,
}

impl LLVMHandle {
    // Currently (and probably forever) only native compilation is supported
    pub fn for_native_target(source_module: &str) -> Self {
        let mut hdl = LLVMHandle {
            builder: unsafe { LLVMCreateBuilder() },
            module: 0 as _,
            target_triple: LLVMString::new(),
            cpu_name: LLVMString::new(),
            cpu_features: LLVMString::new(),
            owned_strings: Vec::new(),
            builtins: HashMap::new(),
        };

        unsafe {
            hdl.module =
                LLVMModuleCreateWithName(hdl.new_cstr(source_module));

            *hdl.target_triple.raw_mut() = LLVMGetDefaultTargetTriple();

            // Pending release of LLVM 7
            // *hdl.cpu_name.raw_mut() = LLVMGetHostCPUName();
            // *hdl.cpu_features.raw_mut() = LLVMGetHostCPUFeatures();
        }

        hdl
    }

    pub fn add_function(&mut self,
                        name: &str,
                        args: &mut [LLVMTypeRef],
                        ret: LLVMTypeRef,
                        linkage: Option<LLVMLinkage>,
                        alignment: Option<u32>)
                        -> FunctionHandle
    {
        let func;
        unsafe {
            let fn_type = func_type(args, ret);
            func = LLVMAddFunction(self.module, self.new_cstr(name), fn_type);

            if let Some(linkage) = linkage {
                LLVMSetLinkage(func, linkage);
            }

            if let Some(alignment) = alignment {
                LLVMSetAlignment(func, alignment);
            }
        }
        // FIXME: How long does func live?
        FunctionHandle { func }
    }

    // TODO: Any extra declarations here?
    pub fn declare_builtin_function(&mut self,
                                    name: &'static str,
                                    args: &mut [LLVMTypeRef],
                                    ret: LLVMTypeRef)
    {
        let f = self.add_function(name, args, ret, None, None).func;
        match self.builtins.entry(name) {
            Entry::Occupied(_) => panic!("Duplicate builtin function {}", name),
            Entry::Vacant(e) => { e.insert(f); }
        }
    }

    fn new_cstr(&mut self, src: &str) -> *const i8 {
        let owned = CString::new(src).expect("LLVM CString");
        let ptr = owned.as_c_str().as_ptr();
        self.owned_strings.push(owned);
        ptr
    }

    //
    // Basic block
    //

    pub fn new_block(&mut self, func: &FunctionHandle, name: &str) -> LLVMBasicBlockRef {
        unsafe {
            LLVMAppendBasicBlock(func.func, self.new_cstr(name))
        }
    }

    pub fn enter_block(&mut self, bb: LLVMBasicBlockRef) {
        unsafe {
            LLVMPositionBuilderAtEnd(self.builder, bb);
        }
    }

    //
    // Values
    //
    pub fn const_uint(&self, ty: LLVMTypeRef, n: u64) -> LLVMValueRef {
        let sign_extend = 0;
        unsafe {
            LLVMConstInt(ty, n, sign_extend)
        }
    }

    pub fn const_float(&self, ty: LLVMTypeRef, n: f64) -> LLVMValueRef {
        unsafe {
            LLVMConstReal(ty, n)
        }
    }

    //
    // Instructions
    //
    pub fn build_alloca(&mut self, ty: LLVMTypeRef, name: &str) -> LLVMValueRef {
        unsafe {
            let name = self.new_cstr(name);
            LLVMBuildAlloca(self.builder, ty, name)
        }
    }

    pub fn build_br(&mut self, bb: LLVMBasicBlockRef) {
        unsafe {
            LLVMBuildBr(self.builder, bb);
        }
    }

    pub fn build_call(&mut self,
                      fn_val: LLVMValueRef,
                      args: &mut [LLVMValueRef],
                      name: &str)
                      -> LLVMValueRef
    {
        let i64t = int64_type();
        let len = args.len() as u32;
        unsafe {
            LLVMBuildCall(self.builder, fn_val, args.as_mut_ptr(), len, self.new_cstr(name))
        }
    }

    // Call a builtin that takes two Rockstar values and returns one
    pub fn build_call_builtin2(&mut self,
                               builtin: &str,
                               arg1: LLVMValueRef,
                               arg2: LLVMValueRef,
                               name: &str)
                               -> LLVMValueRef
    {
        let fn_val = self.builtin_ptr(builtin);
        let args = &mut [arg1, arg2];
        self.build_call(fn_val, args, name)
    }

    pub fn build_call_say(&mut self, arg: LLVMValueRef) {
        let fn_val = self.builtin_ptr("roll_say");
        self.build_call(fn_val, &mut [arg], "");
    }

    pub fn build_call_coerce_function(&mut self, arg: LLVMValueRef, name: &str)
        -> LLVMValueRef
    {
        let fn_val = self.builtin_ptr("roll_coerce_function");
        self.build_call(fn_val, &mut [arg], name)
    }

    pub fn builtin_ptr(&self, name: &str) -> LLVMValueRef {
        *self.builtins.get(name).expect("Builtin lookup")
    }

    pub fn build_cond_br(&mut self,
                         val: LLVMValueRef,
                         bb1: LLVMBasicBlockRef,
                         bb2: LLVMBasicBlockRef)
    {
        unsafe {
            LLVMBuildCondBr(self.builder, val, bb1, bb2);
        }
    }

    pub fn add_global(&mut self,
                      ty: LLVMTypeRef,
                      name: &str,
                      initial_value: Option<LLVMValueRef>,
                      linkage: Option<LLVMLinkage>,
                      alignment: Option<u32>)
        -> LLVMValueRef
    {
        unsafe {
            let global = LLVMAddGlobal(self.module, ty, self.new_cstr(name));

            if let Some(initial_value) = initial_value {
                LLVMSetInitializer(global, initial_value);
            }

            if let Some(linkage) = linkage {
                LLVMSetLinkage(global, LLVMLinkage::LLVMPrivateLinkage);
            }

            if let Some(alignment) = alignment {
                LLVMSetAlignment(global, alignment);
            }

            global
        }
    }

    pub fn build_const_string_ptr(&mut self, value: &str, name: &str) -> LLVMValueRef {
        let c_value = self.new_cstr(value);

        // Anticipate null terminator
        // XXX: Are there efficiency gains from letting LLVM do the null
        // termination?
        let value_len = (value.as_bytes().len() + 1) as u32;
        let dont_null_terminate = 1;

        unsafe {
            let const_str = LLVMConstString(c_value, value_len, dont_null_terminate);

            let global = self.add_global(
                LLVMArrayType(LLVMInt8Type(), value_len),
                name,
                Some(const_str),
                Some(LLVMLinkage::LLVMPrivateLinkage),
                // Needed for tagging
                Some(8),
            );

            LLVMSetGlobalConstant(global, 1);

            global
        }
    }

    pub fn build_in_bounds_get_elem_ptr(&mut self,
                                        ptr: LLVMValueRef,
                                        indices: &mut [LLVMValueRef],
                                        name: &str)
        -> LLVMValueRef
    {
        unsafe {
            LLVMBuildInBoundsGEP(self.builder,
                                 ptr,
                                 indices.as_mut_ptr(),
                                 indices.len() as u32,
                                 self.new_cstr(name))
        }

    }

    pub fn build_load(&mut self, ptr: LLVMValueRef, name: &str) -> LLVMValueRef {
        unsafe {
            LLVMBuildLoad(self.builder, ptr, self.new_cstr(name))
        }
    }

    pub fn build_lshr(&mut self,
                      target: LLVMValueRef,
                      amount: LLVMValueRef,
                      name: &str)
        -> LLVMValueRef
    {
        unsafe {
            LLVMBuildLShr(self.builder, target, amount, self.new_cstr(name))
        }
    }

    pub fn build_int_to_ptr(&mut self,
                            val: LLVMValueRef,
                            dest_ty: LLVMTypeRef,
                            name: &str)
        -> LLVMValueRef
    {
        unsafe {
            LLVMBuildIntToPtr(self.builder, val, dest_ty, self.new_cstr(name))
        }
    }

    pub fn build_ptr_to_int(&mut self,
                            val: LLVMValueRef,
                            dest_ty: LLVMTypeRef,
                            name: &str)
        -> LLVMValueRef
    {
        unsafe {
            LLVMBuildPtrToInt(self.builder, val, dest_ty, self.new_cstr(name))
        }
    }

    pub fn build_return(&mut self, arg: LLVMValueRef) {
        unsafe {
            LLVMBuildRet(self.builder, arg);
        }
    }

    pub fn build_store(&mut self, val: LLVMValueRef, ptr: LLVMValueRef) -> LLVMValueRef {
        unsafe {
            LLVMBuildStore(self.builder, val, ptr)
        }
    }

    pub fn build_switch(&mut self,
                        value: LLVMValueRef,
                        default_block: LLVMBasicBlockRef,
                        num_cases: u32)
                        -> LLVMValueRef
    {
        unsafe {
            LLVMBuildSwitch(self.builder, value, default_block, num_cases)
        }
    }

    pub fn add_case(&mut self,
                    switch_inst: LLVMValueRef,
                    value: LLVMValueRef,
                    block: LLVMBasicBlockRef)
    {
        unsafe {
            LLVMAddCase(switch_inst, value, block);
        }
    }

    pub fn build_trunc(&mut self,
                       val: LLVMValueRef,
                       trunc: LLVMTypeRef,
                       name: &str)
        -> LLVMValueRef
    {
        unsafe {
            LLVMBuildTrunc(self.builder, val, trunc, self.new_cstr(name))
        }
    }

    pub fn build_xor(&mut self,
                     arg1: LLVMValueRef,
                     arg2: LLVMValueRef,
                     name: &str)
                     -> LLVMValueRef
    {
        unsafe {
            LLVMBuildXor(self.builder, arg1, arg2, self.new_cstr(name))
        }
    }

    pub fn finalize(mut self, opts: &super::CodegenOptions)
        -> Result<(), CodegenError>
    {
        use llvm::analysis::*;

        // Verify module
        unsafe {
            let mut err = LLVMError::new();

            let retval = LLVMVerifyModule(
                self.module,
                LLVMVerifierFailureAction::LLVMReturnStatusAction,
                err.raw_mut(),
            );

            let res = err.into_result(retval);

            match res {
                Ok(()) => {}
                Err(_) => LLVMDumpModule(self.module),
            }

            res?;
        }

        unsafe {
            // TODO: Support cross-compilation
            // TODO: Error checking
            LLVM_InitializeNativeTarget();
            LLVM_InitializeNativeAsmPrinter();

            let mut target = 0 as _;
            let mut err = LLVMError::new();

            let retcode = LLVMGetTargetFromTriple(
                self.target_triple.raw(),
                &mut target,
                err.raw_mut(),
            );
            err.into_result(retcode)?;

            assert!(!target.is_null());

            let target_machine =
                LLVMCreateTargetMachine(target,
                                        self.target_triple.raw(),
                                        b"generic\0".as_ptr() as *const _,
                                        b"\0".as_ptr() as *const _,
                                        LLVMCodeGenOptLevel::LLVMCodeGenLevelAggressive,
                                        LLVMRelocMode::LLVMRelocDefault,
                                        LLVMCodeModel::LLVMCodeModelDefault);

            LLVMSetTarget(self.module, self.target_triple.raw());

            let data_layout = LLVMCreateTargetDataLayout(target_machine);
            LLVMSetModuleDataLayout(self.module, data_layout);

            optimise_ir(self.module, opts.opt_level);

            if opts.llvm_dump {
                LLVMDumpModule(self.module);
            }

            if let Some(p) = &opts.output {
                let mut err = LLVMError::new();

                let retcode = LLVMTargetMachineEmitToFile(
                    target_machine,
                    self.module,
                    self.new_cstr(&p) as _,
                    LLVMCodeGenFileType::LLVMObjectFile,
                    err.raw_mut(),
                );

                err.into_result(retcode)?;
            }
        }

        Ok(())
    }
}

#[must_use]
struct LLVMError(LLVMString);

impl LLVMError {
    fn new() -> Self {
        LLVMError(LLVMString::new())
    }

    fn raw_mut(&mut self) -> &mut *mut i8 {
        self.0.raw_mut()
    }

    fn into_result(self, retcode: i32) -> Result<(), CodegenError> {
        let errmsg = self.0.to_string_lossy();

        if retcode == 0 {
            assert!(errmsg.map_or(true, |s| s == ""),
                    "Unexpected error message from LLVM on successful return");
            Ok(())
        } else {
            let errmsg = errmsg.expect("LLVM error message");
            Err(CodegenError::LLVMError(errmsg))
        }
    }
}

struct LLVMString {
    inner: *mut i8,
}

impl LLVMString {
    fn new() -> Self {
        LLVMString {
            inner: 0 as *mut _,
        }
    }

    fn raw(&self) -> *const i8 {
        self.inner as *const i8
    }

    fn raw_mut(&mut self) -> &mut *mut i8 {
        &mut self.inner
    }

    fn as_cstr(&self) -> Option<&CStr> {
        if self.inner.is_null() {
            None
        } else {
            unsafe {
                Some(CStr::from_ptr(self.inner))
            }
        }
    }

    fn to_string_lossy(&self) -> Option<String> {
        self.as_cstr().map(|s| s.to_string_lossy().into_owned())
    }
}

impl Drop for LLVMString {
    fn drop(&mut self) {
        if !self.inner.is_null() {
            unsafe { LLVMDisposeMessage(self.inner) };
        }
    }
}

struct LLVMTargetData {
    inner: LLVMTargetDataRef,
}

impl LLVMTargetData {
    fn new() -> Self {
        LLVMTargetData {
            inner: 0 as *mut _,
        }
    }

    fn raw_mut(&mut self) -> &mut LLVMTargetDataRef {
        &mut self.inner
    }

    fn raw(&mut self) -> LLVMTargetDataRef {
        self.inner
    }
}

impl Drop for LLVMTargetData {
    fn drop(&mut self) {
        if !self.inner.is_null() {
            unsafe { LLVMDisposeTargetData(self.inner) };
        }
    }
}

// FIXME: Error checking
fn optimise_ir(module: *mut LLVMModule, llvm_opt: u32) {
    use llvm::transforms::pass_manager_builder::*;

    unsafe {
        let builder = LLVMPassManagerBuilderCreate();

        LLVMPassManagerBuilderSetOptLevel(builder, llvm_opt);

        let pass_manager = LLVMCreatePassManager();
        LLVMPassManagerBuilderPopulateModulePassManager(builder, pass_manager);

        LLVMPassManagerBuilderDispose(builder);

        // Run twice. This is a hack, we should really work out which
        // optimisations need to run twice. See
        // http://llvm.org/docs/Frontend/PerformanceTips.html#pass-ordering
        LLVMRunPassManager(pass_manager, module);
        LLVMRunPassManager(pass_manager, module);

        LLVMDisposePassManager(pass_manager);
    }
}

impl Drop for LLVMHandle {
    fn drop(&mut self) {
        unsafe {
            if !self.builder.is_null() {
                LLVMDisposeBuilder(self.builder);
            }
            if !self.module.is_null() {
                LLVMDisposeModule(self.module);
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct FunctionHandle {
    func: LLVMValueRef,
}

impl FunctionHandle {
    pub fn param(&self, idx: usize) -> LLVMValueRef {
        unsafe {
            LLVMGetParam(self.func, idx as u32)
        }
    }

    pub fn func_ref(&self) -> LLVMValueRef {
        self.func
    }
}

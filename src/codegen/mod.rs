use std::error;
use std::fmt;

#[macro_use] mod llvm_api;
mod lower_llvm;
mod simple_ir;

use super::BINARY_NAME;
use base_analysis::ScopeMap;
use ast::Statement;

pub use self::lower_llvm::CodegenOptions;
pub use self::simple_ir::dump_ir;

pub fn lower_llvm(program: &[Statement],
                  scope_map: &ScopeMap,
                  opts: &CodegenOptions)
    -> Result<(), CodegenError>
{
    let ir = simple_ir::build_ir(program, scope_map);
    lower_llvm::lower_ir(&ir, opts)
}

#[derive(Debug)]
pub enum CodegenError {
    #[allow(unused)]
    UnsupportedTarget { target: String, is_native_target: bool },
    LLVMError(String),
}

impl CodegenError {
    pub fn is_internal(&self) -> bool {
        match self {
            CodegenError::UnsupportedTarget { .. } => false,
            CodegenError::LLVMError(..) => true,
        }
    }
}

impl error::Error for CodegenError {}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CodegenError::UnsupportedTarget { target, is_native_target } => {
                write!(f, "Compiling to machine code on {} is not currently supported.", target)?;
                if *is_native_target {
                    write!(f, "\n\nTry executing your program using '{} run \
                               <program>' instead", BINARY_NAME)?;
                }
                Ok(())
            }
            CodegenError::LLVMError(msg) => {
                write!(f, "Exception from LLVM: {}", msg)
            }
        }
    }
}

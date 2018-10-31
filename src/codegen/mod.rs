use std::error;
use std::fmt;

#[macro_use] mod llvm_api;
mod lower_llvm;
mod simple_ir;
mod link;

use base_analysis::ScopeMap;
use syntax::ast::Statement;
use runtime_error::RuntimeError;

pub use self::lower_llvm::CodegenOptions;
pub use self::simple_ir::dump_ir;
pub use self::link::perform_link;

pub fn lower_llvm(program: &[Statement],
                  scope_map: &ScopeMap,
                  opts: &CodegenOptions)
    -> Result<(), RuntimeError>
{
    let ir = simple_ir::build_ir(program, scope_map)?;
    lower_llvm::lower_ir(&ir, opts)?;
    Ok(())
}

#[derive(Debug)]
pub enum CodegenError {
    LinkingFailed { exit_status: Option<i32>, stderr: String },
    LLVMError(String),
}

impl CodegenError {
    pub fn is_internal(&self) -> bool {
        match self {
            CodegenError::LinkingFailed { .. } => false,
            CodegenError::LLVMError(..) => true,
        }
    }
}

impl error::Error for CodegenError {}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CodegenError::LinkingFailed { exit_status, stderr } => {
                if let Some(code) = exit_status {
                    write!(f, "Linking the final executable failed with code {}", code)?;
                } else {
                    write!(f, "Linking the final excutable failed (linker interrupted)")?;
                }
                if !stderr.is_empty() {
                    write!(f, "\n{}", stderr)?;
                }
                Ok(())
            }
            CodegenError::LLVMError(msg) => {
                write!(f, "Exception from LLVM: {}", msg)
            }
        }
    }
}

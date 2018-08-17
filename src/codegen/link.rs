use std::mem;
use std::path::Path;
use std::process::Command;

use runtime_error::RuntimeError;
use codegen::CodegenError;

pub fn perform_link(output: &Path, source_object: &Path, runtime: &Path) -> Result<(), RuntimeError> {
    let linker = Linker::native()?;

    let out = Command::new(linker.cmd)
        .args(&linker.opts)
        .arg("-o")
        .arg(output)
        .args(&[source_object, runtime])
        .output()?;

    if out.status.success() {
        Ok(())
    } else {
        Err(CodegenError::LinkingFailed {
            exit_status: out.status.code(),
            stderr: String::from_utf8_lossy(&out.stderr).into(),
        }.into())
    }
}

#[derive(Debug)]
struct Linker {
    cmd: &'static str,
    opts: Vec<&'static str>,
}

impl Linker {
    // Shell out to the C compiler. Should probably use MSVC eventually, but
    // I think this would work as written with MinGW.
    pub fn native() -> Result<Linker, CodegenError> {
        let target_size_opt = match mem::size_of::<usize>() {
            4 => "-m32",
            8 => "-m64",
            n => {
                return Err(CodegenError::UnsupportedTarget {
                    target: format!("{}-bit platform", n * 8),
                    is_native_target: true,
                })
            }
        };

        Ok(Linker {
            cmd: "cc",
            opts: vec![target_size_opt],
        })
    }
}

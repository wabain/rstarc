use core::fmt;

use libc;

const STDOUT_FD: i32 = 1;
const STDERR_FD: i32 = 2;

pub struct FDWrite {
    fd: i32,
}

impl FDWrite {
    pub fn stdout() -> Self {
        FDWrite { fd: STDOUT_FD }
    }

    pub fn stderr() -> Self {
        FDWrite { fd: STDERR_FD }
    }
}

impl fmt::Write for FDWrite {
    fn write_str(&mut self, s: &str) -> fmt::Result {
        // TODO: Don't need locking as long as only one thread is running
        // but this should probably do locking eventually

        let buf = s.as_bytes();
        let len = buf.len();
        let ptr = buf.as_ptr();

        let mut written = 0;

        while written < len {
            let res = unsafe {
                let target = ptr.offset(written as isize) as _;
                libc::write(self.fd, target, len - written)
            };

            if res < 0 {
                return Err(fmt::Error);
            }

            written += res as usize;
        }

        Ok(())
    }
}

#[allow(unused)]
macro_rules! dbg {
    ($($toks:tt)*) => {{
        if cfg!(feature = "ad-hoc-debugs") {
            use ::core::fmt::Write;
            let _ = writeln!($crate::io::FDWrite::stderr(), $($toks)*);
        }
    }};
}

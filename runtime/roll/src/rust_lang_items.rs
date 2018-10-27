use core::fmt::Write;
use core::panic::PanicInfo;

use libc::abort;

use io::FDWrite;

#[panic_handler]
fn panic(info: &PanicInfo) -> ! {
    let mut stderr = FDWrite::stderr();
    let _ = writeln!(stderr, "fatal internal error: {}", info);
    unsafe { abort() }
}

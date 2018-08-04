use core::fmt::Write;
use core::panic::PanicInfo;

use io::FDWrite;

// I don't understand why the no_mangle is needed, but some internal linkage
// requires it
#[allow(private_no_mangle_fns)]
#[panic_implementation]
#[no_mangle]
fn panic(info: &PanicInfo) -> ! {
    let mut stderr = FDWrite::stderr();
    let _ = writeln!(stderr, "fatal internal error: {}", info);
    abort()
}

// FIXME: Should trigger a SIGABORT but that's more trouble than it's worth
// right this moment
fn abort() -> ! {
    unsafe { syscall!(EXIT, 127) };
    loop {}
}

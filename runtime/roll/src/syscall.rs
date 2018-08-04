// FIXME: Not sure this works as written
#[allow(unused)]
macro_rules! syscall_ret {
    ($($args:tt)*) => {{
        let ret = syscall!($($args)*);
        if ret > (!4096usize) + 1 {
            Err(-(ret as i32))
        } else {
            Ok(ret)
        }
    }};
}
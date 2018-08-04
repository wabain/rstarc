use core::fmt::Write;

use super::RockstarValue;
use io::FDWrite;

pub fn say(value: RockstarValue) {
    let mut stdout = FDWrite::stdout();
    let _ = match value {
        RockstarValue::String(v) => writeln!(stdout, "{}", v),
        RockstarValue::Number(v) => writeln!(stdout, "{}", v),
        RockstarValue::Null => writeln!(stdout, "null"),
        RockstarValue::Mysterious => writeln!(stdout, "mysterious"),
        RockstarValue::Boolean(true) => writeln!(stdout, "true"),
        RockstarValue::Boolean(false) => writeln!(stdout, "false"),
        RockstarValue::Func => writeln!(stdout, "function"),
    };
}

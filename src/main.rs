extern crate clap;
extern crate lalrpop_util;
#[macro_use] extern crate lazy_static;
extern crate regex;
extern crate void;

mod ast;
mod lexer;
mod parser;
mod pretty_print;
mod runtime_error;
mod source_loc;

use std::process;
use std::io;
use std::fs::File;

use runtime_error::RuntimeError;
use lexer::{LexicalError, Tokenizer};

fn main() {
    let matches = clap::App::new("rstarc")
        .about("A Rockstar compiler")
        .arg_from_usage("-o --output=[file] 'The output file'")
        .arg_from_usage("-f --format=[pretty|tokens] 'The output format'")
        .arg_from_usage("<source> 'Source file'")  // TODO allow multiple?
        .get_matches();

    let source = matches.value_of("source").expect("arg source");
    let output = matches.value_of("output").unwrap_or("a.out");
    let format = matches.value_of("format");

    let (tokenizer, err) = match load_source(source) {
        Ok(tokenizer) => {
            let err = run(&tokenizer, output, format).err();
            (Some(tokenizer), err)
        }
        Err(e) => (None, Some(e.into())),
    };

    if let Some(err) = err {
        eprintln!("{}", err);

        if let Some((start, end)) = err.span() {
            if let Some(t) = tokenizer {
                eprintln!("");
                eprint_location(&t, start, end);
            }
        }

        process::exit(1);
    }
}

fn load_source(source: &str) -> io::Result<Tokenizer> {
    let mut src_buf = File::open(source)?;
    Ok(Tokenizer::from_file(&mut src_buf)?)
}

fn run(tokenizer: &Tokenizer, output: &str, format: Option<&str>) -> Result<(), RuntimeError> {
    if format == Some("tokens") {
        output_tokens(&tokenizer, output)?;
        return Ok(());
    }

    let tree = parser::ProgramParser::new().parse(tokenizer.tokenize())?;

    match format {
        Some("pretty") => pretty_print::pretty_print_program(io::stdout(), &tree)?,
        _ => { /* TODO */ }
    }

    Ok(())
}

fn output_tokens(tokenizer: &Tokenizer, output: &str) -> Result<(), LexicalError> {
    let tokens = tokenizer.tokenize().collect::<Result<Vec<_>, _>>()?;
    for (start, ref token, end) in &tokens {
        println!("{}..{} {}", start, end, token);
    }
    Ok(())
}

fn eprint_location(tokenizer: &Tokenizer, start: usize, end: usize) {
    let span = tokenizer.get_line_span(start, end);

    let line_meta = format!("{}:  ", span.lineno);

    // FIXME: Going by number of chars does't work for combining diacritics,
    // double-length glyphs, etc.
    eprintln!("{}{}", line_meta, span.line);
    for _ in 0..(line_meta.len() + span.leading_chars()) {
        eprint!(" ");
    }

    let print_range = match span.spanned_chars() {
        0 => 1,
        n => n,
    };

    for _ in 0..print_range {
        eprint!("^");
    }
    eprintln!("");
}

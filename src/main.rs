extern crate clap;
extern crate lalrpop_util;
#[macro_use] extern crate lazy_static;
extern crate regex;

mod ast;
mod lexer;
mod parser;
mod pretty_print;

use std::io;
use std::fs::File;

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

    // FIXME: Error handling
    run(source, output, format).expect("Compilation failed");
}

fn run(source: &str, output: &str, format: Option<&str>) -> io::Result<()> {
    let tokenizer = {
        let mut src_buf = File::open(source)?;
        lexer::Tokenizer::from_file(&mut src_buf)?
    };

    if format == Some("tokens") {
        output_tokens(&tokenizer, output);
        return Ok(());
    }

    let tree = compile(&tokenizer, output).expect("Compilation failed");

    match format {
        Some("pretty") => pretty_print::pretty_print_program(io::stdout(), &tree)?,
        _ => { /* TODO */ }
    }

    Ok(())
}

fn output_tokens(tokenizer: &lexer::Tokenizer, output: &str) {
    let tokens = tokenizer.tokenize().collect::<Result<Vec<_>, _>>().unwrap();
    for (start, ref token, end) in &tokens {
        println!("{}..{} {}", start, end, token);
    }
}

fn compile(tokenizer: &lexer::Tokenizer, output: &str) -> io::Result<Vec<ast::Statement>>
{
    match parser::ProgramParser::new().parse(tokenizer.tokenize()) {
        Ok(tree) => {
            Ok(tree)
        },
        Err(e) => {
            match e {
                lalrpop_util::ParseError::InvalidToken { .. } => {
                    eprintln!("error: invalid token");
                }
                lalrpop_util::ParseError::UnrecognizedToken { ref token, ref expected } => {
                    let tok_desc = if let Some((_, ref tok, _)) = *token {
                        format!("{}", tok)
                    } else {
                        "<none>".into()
                    };

                    eprintln!("error: unexpected token {}", tok_desc);

                    if !expected.is_empty() {
                        eprint!("expected: ");
                        for (i, exp) in expected.iter().enumerate() {
                            if i > 0 {
                                eprint!(", ");
                            }
                            eprint!("{}", exp.replace("\\\\", "\\"));
                        }
                        eprintln!("")
                    }

                    if let Some((start, _, end)) = *token {
                        eprintln!("");
                        eprint_location(&tokenizer, start, end);
                    }
                }
                lalrpop_util::ParseError::ExtraToken { .. } => {
                    eprintln!("error: extra token");
                }
                lalrpop_util::ParseError::User {
                    error: lexer::LexicalError::UnexpectedInput(start, end)
                } => {
                    eprintln!("error: unexpected input");
                    eprintln!("");
                    eprint_location(&tokenizer, start, end);
                }
            }

            Err(io::Error::new(io::ErrorKind::Other, Box::new(e)))
        }
    }
}

fn eprint_location(tokenizer: &lexer::Tokenizer, start: usize, end: usize) {
    let (line, lineno, t_start, t_end) = tokenizer.get_location(start, end);
    let line_formatted = format!("{}:  ", lineno);
    eprintln!("{}{}", line_formatted, line);
    for _ in 0..(line_formatted.len() + t_start) {
        eprint!(" ");
    }
    for _ in 0..(t_end - t_start) {
        eprint!("^");
    }
    eprintln!("");
}

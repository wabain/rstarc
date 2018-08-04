extern crate clap;
extern crate lalrpop_util;
#[macro_use] extern crate lazy_static;
extern crate llvm_sys as llvm;
extern crate regex;
extern crate void;

mod ast;
mod ast_walker;
mod codegen;
mod lang_constructs;
mod lexer;
mod interpreter;
mod parser;
mod pretty_print;
mod runtime_error;
mod source_loc;
mod base_analysis;

use std::process;
use std::io;
use std::fs::File;

use runtime_error::RuntimeError;
use lexer::{LexicalError, Tokenizer};

pub const BINARY_NAME: &str = "rstarc";

enum Action {
    Interpret,
    FormatTokens,
    FormatPretty,
    DumpIR,
    DumpLLVM,
}

fn main() {
    let matches = clap::App::new(BINARY_NAME)
        .about("A Rockstar compiler")

        .settings(&[
            clap::AppSettings::SubcommandRequired,
            clap::AppSettings::VersionlessSubcommands,
        ])

        .subcommand(clap::SubCommand::with_name("run")
            .about("Run the specified program")
            .arg_from_usage("<source> 'The source file'"))

        .subcommand(clap::SubCommand::with_name("internal")
            .about("Internal debugging utilities")
            .arg(clap::Arg::from_usage("-f, --format <FORMAT>  'Debug output format.'")
                    .possible_values(&["tokens", "pretty", "ir", "llvm"]))
            .arg_from_usage("<source> 'The source file'"))

        .get_matches();

    let action;
    let source;

    match matches.subcommand() {
        ("run", Some(submatches)) => {
            source = submatches.value_of("source").expect("arg source");
            action = Action::Interpret;
        }
        ("internal", Some(submatches)) => {
            source = submatches.value_of("source").expect("arg source");
            match submatches.value_of("format") {
                Some("tokens") => action = Action::FormatTokens,
                Some("pretty") => action = Action::FormatPretty,
                Some("ir") => action = Action::DumpIR,
                Some("llvm") => action = Action::DumpLLVM,
                _ => unreachable!(),
            }
        }
        (subcmd, _) => unreachable!("subcommand {}", subcmd),
    }

    let (tokenizer, err) = match load_source(source) {
        Ok(tokenizer) => {
            let err = run(source, &tokenizer, action).err();
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

fn run(source: &str, tokenizer: &Tokenizer, action: Action) -> Result<(), RuntimeError> {
    if let Action::FormatTokens = action {
        output_tokens(&tokenizer)?;
        return Ok(());
    }

    let tree = parser::ProgramParser::new().parse(tokenizer.tokenize())?;
    base_analysis::verify_control_flow(&tree)?;
    let scope_map = base_analysis::identify_variable_scopes(&tree);

    match action {
        Action::Interpret => interpreter::interpret(&tree, &scope_map),
        Action::FormatPretty => pretty_print::pretty_print_program(io::stdout(), &tree)?,
        Action::FormatTokens => unreachable!(),
        Action::DumpIR => codegen::dump_ir(&tree, &scope_map),
        Action::DumpLLVM => {
            let opts = &codegen::CodegenOptions {
                source_file: source,
                llvm_dump: true,
                output: None,
                opt_level: 3,
            };
            codegen::lower_llvm(&tree, &scope_map, opts)?;
        }
    }

    Ok(())
}

fn output_tokens(tokenizer: &Tokenizer) -> Result<(), LexicalError> {
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

#[macro_use] extern crate clap;
#[macro_use] extern crate lalrpop_util;
#[macro_use] extern crate lazy_static;
extern crate bytes;
extern crate llvm_sys as llvm;
extern crate regex;
extern crate tempdir;
extern crate void;
#[cfg(unix)] extern crate libc;
#[macro_use] extern crate smallvec;
extern crate rstarc_types;

mod base_analysis;
mod codegen;
mod lang_constructs;
mod interpreter;
mod runtime_error;
mod syntax;

use std::borrow::Cow;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio, ExitStatus};
use std::process;
use std::io;
use std::fs::File;

use tempdir::TempDir;

use runtime_error::RuntimeError;
use syntax::lexer::{LexicalError, Tokenizer};

pub(crate) const BINARY_NAME: &str = "rstarc";

fn main() {
    let action = build_action(&build_cli().get_matches());

    let res = load_source(&action.source)
        .map_err(|e| (e.into(), None))
        .and_then(|tokenizer| {
            run(&action, &tokenizer).map_err(|e| match e {
                MainError::Runtime(err) => (err, Some(tokenizer)),
                MainError::TokenizerOverride(err, tok) => (err, Some(tok)),
            })
        });

    match res {
        Ok(code) => process::exit(code.unwrap_or(0)),
        Err((err, toks)) => report_error_and_exit(err, toks.as_ref()),
    }
}

enum MainError {
    Runtime(RuntimeError),
    TokenizerOverride(RuntimeError, Tokenizer),
}

impl<T> From<T> for MainError where T: Into<RuntimeError> {
    fn from(err: T) -> Self {
        MainError::Runtime(err.into())
    }
}

fn report_error_and_exit(err: RuntimeError, tokenizer: Option<&Tokenizer>) -> ! {
    eprintln!("{}", err);

    if let Some((start, end)) = err.span() {
        if let Some(t) = tokenizer {
            eprintln!("");
            eprint_location(&t, start, end);
        }
    }

    process::exit(1);
}

fn build_cli() -> clap::App<'static, 'static> {
    let arg_source = clap::Arg::from_usage("<source> 'The source file'");
    let arg_opt_level = clap::Arg::from_usage(
        "-O [LEVEL] \
            'Select the optimization level. Valid values are 0 (no \
            optimization) to 3 (aggressive optimization).'")
        .validator(validate_opt_level);

    let compilation_args = &[
        arg_source.clone(),

        clap::Arg::from_usage(
            "-e, --emit [FORMAT]
             'Comma separated list of types of output to emit. Valid \
              values: obj, exec.'"
        ).validator(validate_emit),

        clap::Arg::from_usage(
            "-o, --output [FILENAME]
             'Write output to filename. If no filename is specified one is \
              selected based on the input filename. If output types other \
              than exec are selected, output filenames are adjusted to \
              have the standard extension for the other formats.'"
        ),

        arg_opt_level.clone(),
    ];

    clap::App::new(BINARY_NAME)
        .about("A Rockstar compiler")

        .settings(&[
            clap::AppSettings::SubcommandRequired,
            clap::AppSettings::VersionlessSubcommands,
        ])

        .subcommand(clap::SubCommand::with_name("run")
            .about("Run the specified program. By default the program will \
                    be compiled into machine code and then executed.")
            .args(compilation_args)
            .arg_from_usage("--interpret \
                             'Run the code in an interpreter instead of \
                              compiling to binary output.'")
        )

        .subcommand(clap::SubCommand::with_name("build")
            .about("Compile the specified program into an executable.")
            .args(compilation_args)
        )

        .subcommand(clap::SubCommand::with_name("internal")
            .about("Internal debugging utilities.")
            .args(&[arg_source, arg_opt_level])
            .arg(clap::Arg::from_usage("-d, --debug-print <FORMAT> 'Print debug output.'")
                .possible_values(&[
                    "tokens",
                    "pretty",
                    "pretty-iterated",
                    "ast",
                    "ir",
                    "ir-repr",
                    "llvm",
                ]))
        )
}

fn validate_emit(emit: String) -> Result<(), String> {
    if emit.is_empty() {
        return Ok(());
    }

    for v in emit.split(",") {
        match v {
            "exec" | "obj" => {}
            _ => return Err(
                format!("unknown emission type '{}' (expected one of: 'exec', \
                         'obj')", v),
            ),
        }
    }

    Ok(())
}

fn validate_opt_level(opt_level: String) -> Result<(), String> {
    match opt_level.parse::<u32>() {
        Err(_) => Err(format!("Expected a number from 0 to 3")),
        Ok(i) if i <= 3 => Ok(()),
        Ok(i) => Err(format!("Unsupported optimization level {} (supported \
                              values are 0 to 3)", i))
    }
}

#[derive(Debug, Clone, PartialEq)]
struct Action {
    source: String,
    execution_mode: Option<ExecutionMode>,
    compile_options: Option<CompileOptions>,
    debug_output: Option<DebugOutputFormat>,
}

impl Action {
    fn interpret_or_compile(&self) -> bool {
        self.execution_mode.is_some() || self.compile_options.is_some()
    }

    fn needs_ast_pass(&self) -> bool {
        if self.interpret_or_compile() {
            return true;
        }

        match self.debug_output {
            Some(DebugOutputFormat::Tokens) | None => false,
            Some(_) => true,
        }
    }

    fn needs_scope_analysis_pass(&self) -> bool {
        if !self.needs_ast_pass() {
            return false;
        }

        if self.interpret_or_compile() {
            return true;
        }

        match self.debug_output {
            Some(DebugOutputFormat::Pretty { .. }) |
            Some(DebugOutputFormat::AST) => false,
            _ => true,
        }
    }

    fn needs_lowering_pass(&self) -> bool {
        self.compile_options.is_some()
    }

    fn needs_linking(&self) -> bool {
        self.compile_options.as_ref().map_or(false, |c| {
            c.exec_output.is_some()
        })
    }
}

#[derive(Debug, Clone, PartialEq)]
struct CompileOptions {
    exec_output: Option<CompilerOutput>,
    obj_output: Option<CompilerOutput>,
    opt_level: u32,
}

#[derive(Debug, Clone, PartialEq)]
enum CompilerOutput {
    UserPath(PathBuf),
    TempFile { filename: String },
}

impl CompilerOutput {
    fn build_path(&self, tmp_dir: &mut Option<TempDir>) -> Result<Cow<Path>, io::Error> {
        match self {
            CompilerOutput::UserPath(p) => Ok(p.into()),
            CompilerOutput::TempFile { filename } => {
                if tmp_dir.is_none() {
                    *tmp_dir = Some(TempDir::new("rockstar-build")?);
                }
                Ok(tmp_dir.as_ref().unwrap().path().join(filename).into())
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum ExecutionMode {
    Interpret,
    SpawnBinary,
}

#[derive(Debug, Copy, Clone, PartialEq)]
enum DebugOutputFormat {
    Tokens,
    Pretty { iterated: bool },
    AST,
    IR,
    IRRepr,
    LLVM,
}

fn build_action(matches: &clap::ArgMatches) -> Action {
    match matches.subcommand() {
        ("run", Some(submatches)) => {
            let source = submatches.value_of("source").expect("arg source");

            let execution_mode = match submatches.is_present("interpret") {
                true => Some(ExecutionMode::Interpret),
                false => Some(ExecutionMode::SpawnBinary),
            };

            Action {
                source: source.to_string(),
                execution_mode,
                compile_options: Some(get_compile_options(
                    submatches,
                    source,
                    &CompilerOptionsBuildFlags {
                        emit_exec_by_default: false,
                        force_exec_build: true,
                    },
                )),
                debug_output: None,
            }
        }
        ("build", Some(submatches)) => {
            let source = submatches.value_of("source").expect("arg source");

            Action {
                source: source.to_string(),
                execution_mode: None,
                compile_options: Some(get_compile_options(
                    submatches,
                    source,
                    &CompilerOptionsBuildFlags {
                        emit_exec_by_default: true,
                        force_exec_build: false,
                    },
                )),
                debug_output: None,
            }
        }
        ("internal", Some(submatches)) => {
            let source = submatches.value_of("source").expect("arg source");

            let debug_output = match submatches.value_of("debug-print") {
                Some("tokens") => Some(DebugOutputFormat::Tokens),
                Some("pretty") => Some(DebugOutputFormat::Pretty { iterated: false }),
                Some("pretty-iterated") => Some(DebugOutputFormat::Pretty { iterated: true }),
                Some("ast") => Some(DebugOutputFormat::AST),
                Some("ir") => Some(DebugOutputFormat::IR),
                Some("ir-repr") => Some(DebugOutputFormat::IRRepr),
                Some("llvm") => Some(DebugOutputFormat::LLVM),
                Some(v) => unreachable!("debug-print format {:?}", v),
                None => unreachable!("no debug-print format"),
            };

            let needs_codegen = debug_output == Some(DebugOutputFormat::LLVM);

            Action {
                source: source.to_string(),
                execution_mode: None,
                compile_options: if needs_codegen {
                    Some(get_compile_options(
                        submatches,
                        source,
                        &CompilerOptionsBuildFlags {
                            emit_exec_by_default: false,
                            force_exec_build: false,
                        },
                    ))
                } else {
                    None
                },
                debug_output,
            }
        }
        (subcmd, _) => unreachable!("subcommand {}", subcmd),
    }
}

#[derive(Debug, Copy, Clone)]
struct CompilerOptionsBuildFlags {
    emit_exec_by_default: bool,
    force_exec_build: bool,
}

fn get_compile_options(submatches: &clap::ArgMatches,
                       source: &str,
                       flags: &CompilerOptionsBuildFlags)
    -> CompileOptions
{
    let mut emit_exec = false;
    let mut emit_obj = false;

    match submatches.value_of("emit") {
        Some(s) if s == "" => {
            // Keep all emit flags false
        }
        Some(s) => {
            for v in s.split(",") {
                match v {
                    "exec" => { emit_exec = true; }
                    "obj" => { emit_obj = true; }
                    _ => unreachable!("emission type {:?}", v),
                }
            }
        }
        None => {
            emit_exec = flags.emit_exec_by_default;
        }
    }

    let output = submatches.value_of("output");

    let exec_output: Option<CompilerOutput>;

    if emit_exec {
        let path = output.map_or_else(
            || swap_extension(source, ""),
            |o| PathBuf::from(o),
        );
        exec_output = Some(CompilerOutput::UserPath(path));
    } else if flags.force_exec_build {
        exec_output = Some(CompilerOutput::TempFile { filename: "out".to_string() });
    } else {
        exec_output = None;
    };

    let obj_output;

    if emit_obj {
        obj_output = Some(CompilerOutput::UserPath(
            swap_extension(output.unwrap_or(source), "o")
        ));
    } else if exec_output.is_some() {
        obj_output = Some(CompilerOutput::TempFile { filename: "out.o".to_string() });
    } else {
        obj_output = None;
    }

    CompileOptions {
        exec_output,
        obj_output,
        opt_level: submatches.value_of("O").map_or(3, |_| {
            value_t!(submatches.value_of("O"), u32)
                .expect("Revalidation of opt_level failed")
        }),
    }
}

fn swap_extension<'a, P>(src_path: P, extension: &str) -> PathBuf
    where P: AsRef<Path>
{
    src_path.as_ref().with_extension(extension)
}

fn load_source(source: &str) -> io::Result<Tokenizer> {
    let mut src_buf = File::open(source)?;
    Ok(Tokenizer::from_file(&mut src_buf)?)
}

fn run(action: &Action, tokenizer: &Tokenizer) -> Result<Option<i32>, MainError> {
    let Action {
        ref source,
        execution_mode,
        debug_output,
        ..
    } = *action;

    if debug_output == Some(DebugOutputFormat::Tokens) {
        output_tokens(&tokenizer)?;
    }

    if !action.needs_ast_pass() {
        return Ok(None);
    }

    let tree = syntax::parser::ProgramParser::new().parse(tokenizer.tokenize())?;
    base_analysis::verify_control_flow(&tree)?;

    match debug_output {
        Some(DebugOutputFormat::Pretty { iterated: false }) => {
            syntax::pretty_print::pretty_print_program(io::stdout(), &tree)?;
        }
        Some(DebugOutputFormat::Pretty { iterated: true }) => {
            output_iterated_pretty_print(&tree)?;
        }
        Some(DebugOutputFormat::AST) => {
            syntax::ast_print::ast_print_program(io::stdout(), &tree)?;
        }
        _ => {}
    }

    if !action.needs_scope_analysis_pass() {
        return Ok(None);
    }

    let scope_map = base_analysis::identify_variable_scopes(&tree);

    // If interpreting, allow compile options to be passed but ignore
    // them
    if execution_mode == Some(ExecutionMode::Interpret) {
        interpreter::interpret(&tree, &scope_map)?;
        return Ok(None);
    }

    match debug_output {
        Some(DebugOutputFormat::IR) => {
            let ir = codegen::build_ir(&tree, &scope_map)?;
            codegen::dump_ir(&ir);
        }
        Some(DebugOutputFormat::IRRepr) => {
            let ir = codegen::build_ir(&tree, &scope_map)?;
            println!("{:?}", &ir);
        }
        // Other debug formats are addressed above or below
        Some(DebugOutputFormat::Tokens) |
        Some(DebugOutputFormat::Pretty { .. }) |
        Some(DebugOutputFormat::AST) |
        Some(DebugOutputFormat::LLVM) |
        None => {}
    }

    if !action.needs_lowering_pass() {
        return Ok(None);
    }

    let compile_options = action.compile_options
        .as_ref()
        .expect("Need compile options for lowering pass");

    let mut tmp_dir = None;

    let obj_output = match &compile_options.obj_output {
        Some(p) => {
            Some(p.build_path(&mut tmp_dir)?)
        }
        None => None,
    };

    let ir = codegen::build_ir(&tree, &scope_map)?;
    let opts = &codegen::CodegenOptions {
        source_file: source,
        llvm_dump: debug_output == Some(DebugOutputFormat::LLVM),
        output: obj_output.as_ref().map(|p| p.to_str().expect("obj path")),
        opt_level: compile_options.opt_level,
    };
    codegen::lower_llvm(&ir, opts)?;

    if !action.needs_linking() {
        return Ok(None);
    }

    let exec_output = compile_options.exec_output
        .as_ref()
        .expect("Linking required but no executable path");
    let exec_output = exec_output.build_path(&mut tmp_dir)?;

    let obj_output = obj_output.expect("Linking required but no object generated");

    codegen::perform_link(
        &exec_output,
        &obj_output,
        &get_runtime_lib_path()?,
    )?;

    if execution_mode == Some(ExecutionMode::SpawnBinary) {
        let status = Command::new(exec_output.as_os_str())
            .stdout(Stdio::inherit())
            .stderr(Stdio::inherit())
            .status()?;

        if !status.success() {
            let code = status.code().unwrap_or_else(|| {
                handle_irregular_child_exit(&status)
            });
            return Ok(Some(code));
        }
    }

    Ok(None)
}

fn output_iterated_pretty_print(tree: &[syntax::ast::Statement]) -> Result<(), MainError> {
    use bytes::BufMut;
    let mut buf_stream = Vec::new().writer();

    syntax::pretty_print::pretty_print_program(&mut buf_stream, tree)?;

    let pretty_src = String::from_utf8(buf_stream.into_inner())
        .expect("Non-UTF8 output from pretty printer");

    let tokenizer = Tokenizer::new(pretty_src);

    syntax::parser::ProgramParser::new().parse(tokenizer.tokenize())
        .map_err(|err| -> RuntimeError { err.into() })
        .and_then(|pretty_tree| {
            syntax::pretty_print::pretty_print_program(io::stdout(), &pretty_tree)
                .map_err(|err| err.into())
        })
        .map_err(|err| {
            eprintln!("Failed to reparse pretty printed output:");
            MainError::TokenizerOverride(err, tokenizer)
        })
}

// FIXME: For now, hardcode a recursion into the runtime release target
// directory.
//
// This is probably not the best choice for the final runtime structure.
fn get_runtime_lib_path() -> Result<PathBuf, RuntimeError> {
    use std::env;
    use std::fs;

    match env::var_os("RSTARC_RUNTIME") {
        Some(ref p) if p.len() > 0 => return Ok(PathBuf::from(p)),
        _ => {}
    }

    let mut lib_path = fs::canonicalize(env::current_exe()?)?;

    lib_path.pop();
    lib_path.pop();
    lib_path.pop();

    lib_path.push("runtime");
    lib_path.push("roll");
    lib_path.push("target");
    lib_path.push("release");
    lib_path.push("libroll.a");

    Ok(lib_path)
}

#[cfg(unix)]
fn handle_irregular_child_exit(status: &ExitStatus) -> i32 {
    use std::os::unix::process::ExitStatusExt;
    use libc::*;

    let sig = match status.signal() {
        Some(s) => s,
        None => return 1,
    };

    // Only match a few maybe likelier things (this is not a carefully curated
    // list)
    let sig_name = match sig {
        SIGABRT => "SIGABRT",
        SIGALRM => "SIGALRM",
        SIGBUS => "SIGBUS",
        SIGHUP => "SIGHUP",
        SIGILL => "SIGILL",
        SIGINT => "SIGINT",
        SIGKILL => "SIGKILL",
        SIGPIPE => "SIGPIPE",
        SIGQUIT => "SIGQUIT",
        SIGSEGV => "SIGSEGV",
        SIGSTOP => "SIGSTOP",
        SIGTERM => "SIGTERM",
        SIGUSR1 => "SIGUSR1",
        SIGUSR2 => "SIGUSR2",
        SIGXCPU => "SIGXCPU",
        SIGXFSZ => "SIGXFSZ",
        _ => {
            eprintln!("Program exited on signal {}", sig);
            return 128 + sig;
        }
    };
    eprintln!("Program exited on signal {} ({})", sig_name, sig);
    128 + sig
}

#[cfg(not(unix))]
fn handle_irregular_child_exit(status: &process::ExitStatus) -> i32 {
    1
}

fn output_tokens(tokenizer: &Tokenizer) -> Result<(), LexicalError> {
    let tokens = tokenizer.tokenize().collect::<Result<Vec<_>, _>>()?;

    let mut lineno = 0;

    for &(start, ref token, end) in &tokens {
        let next_lineno = tokenizer.get_line_for_point(start);
        if lineno != next_lineno {
            if lineno > 0 {
                println!("");
            }

            for lineno in lineno + 1..=next_lineno {
                let line_content = tokenizer.get_line_with_number(lineno);
                println!("{:<4} {}⏎", lineno, line_content);
            }

            println!("");
            lineno = next_lineno;
        }

        let range = format!("{}..{}", start, end);

        let payload = format!("{:?}", token.repr_payload());

        if payload.is_empty() {
            println!("{:>10} {}", range, token);
        } else {
            println!("{:>10} {} {}", range, payload, token.variant_name());
        }
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

#[cfg(test)]
mod main_test {
    use std::path::Path;

    use super::{Action, ExecutionMode, CompileOptions, CompilerOutput, build_cli, build_action};

    macro_rules! match_action {
        ($action:expr, $pat:pat) => {
            match $action {
                $pat => {}
                other => panic!("Unexpected action {:?}", other)
            }
        };
        ($action:expr, $pat:pat => $more:expr) => {
            match $action {
                $pat => $more,
                other => panic!("Unexpected action {:?}", other)
            }
        }
    }

    fn mk_action(args: &[&str]) -> Action {
        let app = build_cli();
        let args = app.get_matches_from_safe(args).unwrap();
        build_action(&args)
    }

    #[test]
    fn test_run_compile() {
        let action = mk_action(&["rstarc", "run", "foo.rock"]);

        match_action!(&action, Action {
            source: _,
            execution_mode: Some(ExecutionMode::SpawnBinary),
            compile_options: Some(CompileOptions {
                exec_output: Some(CompilerOutput::TempFile { .. }),
                obj_output: Some(CompilerOutput::TempFile { .. }),
                opt_level: 3,
            }),
            debug_output: None,
        });
    }

    #[test]
    fn test_run_compile_emit_exec() {
        let action = mk_action(&["rstarc", "run", "--emit", "exec", "foo.rock"]);

        match_action!(&action, Action {
            source: _,
            execution_mode: Some(ExecutionMode::SpawnBinary),
            compile_options: Some(CompileOptions {
                exec_output: Some(CompilerOutput::UserPath(p)),
                obj_output: Some(CompilerOutput::TempFile { .. }),
                opt_level: 3,
            }),
            debug_output: None,
        } => assert_eq!(&p, &Path::new("foo")));
    }

    #[test]
    fn test_run_interpret() {
        // Compilation-related arguments are allowed, although they'll be ignored
        let action = mk_action(&["rstarc", "run", "--interpret", "-O2", "foo.rock"]);

        match_action!(&action, Action {
            source: _,
            execution_mode: Some(ExecutionMode::Interpret),
            compile_options: Some(CompileOptions {
                exec_output: Some(CompilerOutput::TempFile { .. }),
                obj_output: Some(CompilerOutput::TempFile { .. }),
                opt_level: 2,
            }),
            debug_output: None,
        });
    }

    #[test]
    fn test_build_exec() {
        let action = mk_action(&[
            "rstarc", "build", "-o", "bar/baz", "foo.rock"
        ]);

        match_action!(&action, Action {
            source: _,
            execution_mode: None,
            compile_options: Some(CompileOptions {
                exec_output: Some(CompilerOutput::UserPath(p)),
                obj_output: Some(CompilerOutput::TempFile { .. }),
                opt_level: 3,
            }),
            debug_output: None,
        } => assert_eq!(&p, &Path::new("bar/baz")));
    }

    #[test]
    fn test_build_emit_only_obj() {
        let action = mk_action(&[
            "rstarc", "build", "--emit", "obj", "-o", "bar/baz", "foo.rock"
        ]);

        match_action!(&action, Action {
            source: _,
            execution_mode: None,
            compile_options: Some(CompileOptions {
                exec_output: None,
                obj_output: Some(CompilerOutput::UserPath(p)),
                opt_level: 3,
            }),
            debug_output: None,
        } => assert_eq!(&p, &Path::new("bar/baz.o")));
    }

    #[test]
    fn test_build_emit_none() {
        // A weird corner case, but make sure a sensible action is generated at
        // least
        let action = mk_action(&["rstarc", "build", "--emit", "", "foo.rock"]);

        match_action!(&action, Action {
            source: _,
            execution_mode: None,
            compile_options: Some(CompileOptions {
                exec_output: None,
                obj_output: None,
                opt_level: 3,
            }),
            debug_output: None,
        });
    }
}

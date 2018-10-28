//! Defines a simple AST output format
//!
//! Structure is simplified occasionally towards leaf nodes (e.g. with
//! lvalues, literals, etc.) but the output format is otherwise very
//! regular.

use io;
use ast::{Statement, StatementKind, Expr, Logical, Comparison, LValue, Variable};

macro_rules! node {
    ($out:ident, $indent:expr, $e:expr, $($toks:tt)*) => {{
        let indent = $indent;
        writeln!($out, "{}{}(", indented(indent), $e)?;
        node_arg!($out, indent + 1, $($toks)*,);
        writeln!($out, "{}),", indented(indent))?;
    }};
}

macro_rules! node_arg {
    ($out:ident, $indent:expr, $e:expr, $($toks:tt)*) => {{
        let indent = $indent;
        $e.ast_print($out, indent)?;
        node_arg!($out, indent, $($toks)*);
    }};
    ($out:ident, $indent:expr, block $block:expr, $($toks:tt)*) => {{
        let indent = $indent;
        writeln!($out, "{}[", indented(indent))?;
        for e in $block.iter() {
            node_arg!($out, indent + 1, e,);
        }
        writeln!($out, "{}],", indented(indent))?;
        node_arg!($out, indent, $($toks)*);
    }};
    ($out:ident, $indent:expr, term $term:expr, $($toks:tt)*) => {{
        let indent = $indent;
        term!($out, indent, $term);
        node_arg!($out, indent, $($toks)*);
    }};
    ($out:ident, $indent:expr, ) => {};
}

macro_rules! term {
    ($out:ident, $indent:expr, $e:expr) => {{
        writeln!($out, "{}{},", indented($indent), $e)?;
    }};
}

fn indented(indent: usize) -> String {
    "  ".repeat(indent)
}

pub fn ast_print_program<W>(mut out: W, program: &[Statement]) -> io::Result<()>
    where W: io::Write
{
    for statement in program {
        statement.ast_print(&mut out, 0)?;
    }
    Ok(())
}

pub trait AstPrint {
    fn ast_print<W>(&self, &mut W, indent: usize) -> io::Result<()> where W: io::Write;
}

impl AstPrint for Statement {
    fn ast_print<W>(&self, out: &mut W, indent: usize) -> io::Result<()> where W: io::Write {
        match &self.kind {
            StatementKind::Assign(lval, e) => {
                node!(out, indent, "Assign", lval, e)
            }
            StatementKind::Incr(lval) => {
                node!(out, indent, "Incr", lval)
            }
            StatementKind::Decr(lval) => {
                node!(out, indent, "Decr", lval)
            }
            StatementKind::Say(e) => {
                node!(out, indent, "Say", e)
            }
            StatementKind::Continue => {
                term!(out, indent, "Continue")
            }
            StatementKind::Break => {
                term!(out, indent, "Break")
            }
            StatementKind::Return(e) => {
                node!(out, indent, "Return", e)
            }
            StatementKind::Condition(cond, statements, else_statements) => {
                node!(out, indent, "If", cond, block statements, block else_statements);
            }
            StatementKind::While(cond, statements) => {
                node!(out, indent, "While", cond, block statements);
            }
            StatementKind::Until(cond, statements) => {
                node!(out, indent, "Until", cond, block statements);
            }
            StatementKind::FuncDef(fname, vars, statements) => {
                node!(out, indent, "FuncDef", fname, block vars, block statements);
            }
        }

        Ok(())
    }
}

impl AstPrint for Expr {
    fn ast_print<W>(&self, out: &mut W, indent: usize) -> io::Result<()> where W: io::Write {
        match *self {
            Expr::LValue(ref lval) => lval.ast_print(out, indent)?,
            Expr::Literal(ref literal) => term!(out, indent, literal),
            Expr::Compare(ref comp) => comp.ast_print(out, indent)?,

            Expr::FuncCall(ref fname, ref args) => {
                node!(out, indent, "FuncCall", fname, block args)
            }

            Expr::Add(ref e1, ref e2) => node!(out, indent, "Add", e1, e2),
            Expr::Sub(ref e1, ref e2) => node!(out, indent, "Sub", e1, e2),
            Expr::Mul(ref e1, ref e2) => node!(out, indent, "Mul", e1, e2),
            Expr::Div(ref e1, ref e2) => node!(out, indent, "Div", e1, e2),

            Expr::Logical(ref logical) => logical.ast_print(out, indent)?,
        }

        Ok(())
    }
}

impl AstPrint for Logical {
    fn ast_print<W>(&self, out: &mut W, indent: usize) -> io::Result<()> where W: io::Write {
        match *self {
            Logical::Not(ref cond) => node!(out, indent, "Not", cond),
            Logical::And(ref c1, ref c2) => node!(out, indent, "And", c1, c2),
            Logical::Or(ref c1, ref c2) => node!(out, indent, "Or", c1, c2),
            Logical::Nor(ref c1, ref c2) => node!(out, indent, "Nor", c1, c2),
        }

        Ok(())
    }
}

impl AstPrint for Comparison {
    fn ast_print<W>(&self, out: &mut W, indent: usize) -> io::Result<()> where W: io::Write {
        let Comparison(ref e1, comparator, ref e2) = *self;
        let cmp = format!("{:?}", comparator);
        node!(out, indent, "Comparison", e1, term cmp, e2);
        Ok(())
    }
}

impl AstPrint for LValue {
    fn ast_print<W>(&self, out: &mut W, indent: usize) -> io::Result<()> where W: io::Write {
        match *self {
            LValue::Pronoun(ref p) => term!(out, indent, p),
            LValue::Variable(ref v) => v.ast_print(out, indent)?,
        }
        Ok(())
    }
}

impl AstPrint for Variable {
    fn ast_print<W>(&self, out: &mut W, indent: usize) -> io::Result<()> where W: io::Write {
        match *self {
            Variable::CommonVar(ref prep, ref var, _pos) => {
                term!(out, indent, format!("{} {}", prep, var))
            }
            Variable::ProperVar(ref var, _pos) => {
                term!(out, indent, var)
            }
        }
        Ok(())
    }
}

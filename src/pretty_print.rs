use io;
use ast::{Statement, StatementKind, Expr, Logical, Comparison, Comparator, LValue, Variable};

macro_rules! pp {
    ($out:ident, $($toks:tt)*) => ({
        ppentry!($out, $($toks)*,);
    })
}

macro_rules! ppentry {
    ($out:ident, $e:expr, $($toks:tt)*) => (
        write!($out, "{}", $e)?;
        ppentry!($out, $($toks)*)
    );
    ($out:ident, pp $e:expr, $($toks:tt)*) => (
        $e.pretty_print($out)?;
        ppentry!($out, $($toks)*)
    );
    ($out:ident, ) => ();
}

pub fn pretty_print_program<W>(mut out: W, program: &[Statement]) -> io::Result<()>
    where W: io::Write
{
    for statement in program {
        statement.pretty_print(&mut out)?;
    }
    Ok(())
}

pub trait PrettyPrint {
    fn pretty_print<W>(&self, &mut W) -> io::Result<()> where W: io::Write;
}

impl PrettyPrint for Statement {
    fn pretty_print<W>(&self, out: &mut W) -> io::Result<()> where W: io::Write {
        match &self.kind {
            StatementKind::Assign(lval, e) => {
                pp!(out, "Put ", pp e, " into ", pp lval, "\n")
            }
            StatementKind::Incr(lval) => {
                pp!(out, "Build ", pp lval, " up\n")
            }
            StatementKind::Decr(lval) => {
                pp!(out, "Knock ", pp lval, " down\n")
            }
            StatementKind::Say(e) => {
                pp!(out, "Say ", pp e, "\n")
            }
            StatementKind::Continue => {
                pp!(out, "Continue\n")
            }
            StatementKind::Break => {
                pp!(out, "Break\n")
            }
            StatementKind::Return(e) => {
                pp!(out, "Give back ", pp e, "\n")
            }
            StatementKind::Condition(cond, statements, else_statements) => {
                pp!(out, "If ", pp cond, "\n");
                pp_block_no_terminal(out, statements)?;

                if else_statements.is_empty() {
                    pp!(out, "\n");
                } else {
                    pp!(out, "Else\n");
                    pp_block(out, else_statements)?;
                }
            }
            StatementKind::While(cond, statements) => {
                pp!(out, "While ", pp cond, "\n");
                pp_block(out, statements)?;
            }
            StatementKind::Until(cond, statements) => {
                pp!(out, "Until ", pp cond, "\n");
                pp_block(out, statements)?;
            }
            StatementKind::FuncDef(fname, vars, statements) => {
                pp!(out, pp fname, " takes ");
                for (i, v) in vars.iter().enumerate() {
                    if i > 0 {
                        pp!(out, " and ", pp v);
                    } else {
                        pp!(out, pp v);
                    }
                }
                pp!(out, "\n");
                pp_block(out, statements)?;
            }
        }

        Ok(())
    }
}

impl PrettyPrint for Expr {
    fn pretty_print<W>(&self, out: &mut W) -> io::Result<()> where W: io::Write {
        match *self {
            Expr::LValue(ref lval) => lval.pretty_print(out)?,
            Expr::Literal(ref literal) => write!(out, "{}", literal)?,
            Expr::Compare(ref comp) => comp.pretty_print(out)?,

            Expr::FuncCall(ref fname, ref args) => {
                pp!(out, pp fname, " taking ");
                for (i, e) in args.iter().enumerate() {
                    if i > 0 {
                        pp!(out, ", ", pp e);
                    } else {
                        pp!(out, pp e);
                    }
                }
            }

            // Don't need to handle precedence because there's no way
            // to group expressions to have non-default precedence
            Expr::Add(ref e1, ref e2) => pp!(out, pp e1, " plus ", pp e2),
            Expr::Sub(ref e1, ref e2) => pp!(out, pp e1, " minus ", pp e2),
            Expr::Mul(ref e1, ref e2) => pp!(out, pp e1, " times ", pp e2),
            Expr::Div(ref e1, ref e2) => pp!(out, pp e1, " over ", pp e2),
            Expr::Logical(ref logical) => logical.pretty_print(out)?,
        }

        Ok(())
    }
}

impl PrettyPrint for Logical {
    fn pretty_print<W>(&self, out: &mut W) -> io::Result<()> where W: io::Write {
        match *self {
            Logical::Not(ref cond) => pp!(out, "not ", pp cond),
            Logical::And(ref c1, ref c2) => pp!(out, pp c1, " and ", pp c2),
            Logical::Or(ref c1, ref c2) => pp!(out, pp c1, " or ", pp c2),
            Logical::Nor(ref c1, ref c2) => pp!(out, pp c1, " or ", pp c2),
        }

        Ok(())
    }
}

impl PrettyPrint for Comparison {
    fn pretty_print<W>(&self, out: &mut W) -> io::Result<()> where W: io::Write {
        let Comparison(ref e1, comparator, ref e2) = *self;

        e1.pretty_print(out)?;
        write!(out, " ")?;
        match comparator {
            Comparator::Is => write!(out, "is")?,
            Comparator::IsNot => write!(out, "isn't")?,
            Comparator::IsGreaterThan => write!(out, "is greater than")?,
            Comparator::IsLessThan => write!(out, "is less than")?,
            Comparator::IsAsGreatAs => write!(out, "is as great as")?,
            Comparator::IsAsLittleAs => write!(out, "is as little as")?,
        }
        write!(out, " ")?;
        e2.pretty_print(out)
    }
}

impl PrettyPrint for LValue {
    fn pretty_print<W>(&self, out: &mut W) -> io::Result<()> where W: io::Write {
        match *self {
            LValue::Pronoun(ref p) => write!(out, "{}", p),
            LValue::Variable(ref v) => v.pretty_print(out),
        }
    }
}

impl PrettyPrint for Variable {
    fn pretty_print<W>(&self, out: &mut W) -> io::Result<()> where W: io::Write {
        match *self {
            Variable::CommonVar(ref prep, ref var, _pos) => {
                write!(out, "{} {}", prep, var)
            }
            Variable::ProperVar(ref var, _pos) => {
                write!(out, "{}", var)
            }
        }
    }
}

fn pp_block<W>(out: &mut W, statements: &[Statement]) -> io::Result<()>
    where W: io::Write
{
    pp_block_no_terminal(out, statements)?;
    pp!(out, "\n");
    Ok(())
}

fn pp_block_no_terminal<W>(out: &mut W, statements: &[Statement]) -> io::Result<()>
    where W: io::Write
{
    for statement in statements {
        pp!(out, pp statement);
    }
    Ok(())
}

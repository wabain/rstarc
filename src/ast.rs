use std::fmt;
use lexer::Token;
use lang_constructs::LangVariable;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Pos(pub usize, pub usize);

#[derive(Debug)]
pub struct Statement {
    pub kind: StatementKind,
    pub pos: Pos,
}

#[derive(Debug)]
pub enum StatementKind {
    Assign(LValue, Expr),
    Incr(LValue, u32),
    Decr(LValue, u32),
    Say(Expr),

    Continue,
    Break,
    Return(Expr),

    Condition(Expr, Vec<Statement>, Vec<Statement>),
    While(Expr, Vec<Statement>),
    Until(Expr, Vec<Statement>),
    FuncDef(Variable, Vec<Variable>, Vec<Statement>),
}

#[derive(Debug)]
pub enum Expr {
    LValue(LValue),
    Literal(Token),
    Compare(Box<Comparison>),
    FuncCall(Box<Expr>, Vec<Box<Expr>>),

    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
    Mul(Box<Expr>, Box<Expr>),
    Div(Box<Expr>, Box<Expr>),

    Logical(Box<Logical>),
}

impl Expr {
    pub fn compare(comparison: Comparison) -> Self {
        Expr::Compare(Box::new(comparison))
    }

    pub fn logical(logical: Logical) -> Self {
        Expr::Logical(Box::new(logical))
    }
}

#[derive(Debug)]
pub struct Comparison(pub Expr, pub Comparator, pub Expr);

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum Comparator {
    Is,
    IsNot,
    IsGreaterThan,
    IsLessThan,
    IsAsGreatAs,
    IsAsLittleAs,
}

#[derive(Debug)]
pub enum Logical {
    Not(Expr),
    And(Expr, Expr),
    Or(Expr, Expr),
    Nor(Expr, Expr),
}

pub enum LValue {
    Variable(Variable),
    Pronoun(Token),
}

impl fmt::Debug for LValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LValue::Variable(Variable::ProperVar(p, pos)) => write!(f, "ProperVar({} [{:?}])", p, pos),
            LValue::Variable(Variable::CommonVar(p, v, pos)) => write!(f, "CommonVar({} {}, [{:?}])", p, v, pos),
            LValue::Pronoun(p) => write!(f, "Pronoun({})", p),
        }
    }
}

#[derive(Debug)]
pub enum Variable {
    ProperVar(Token, Pos),
    CommonVar(Token, Token, Pos),
}

impl Variable {
    pub fn to_lang_variable<'a>(&'a self) -> LangVariable<'a> {
        match self {
            Variable::CommonVar(prep, common, _pos) => {
                LangVariable::Common(
                    prep.deref_common_prep().into(),
                    common.deref_common_var().into(),
                )
            },
            Variable::ProperVar(proper, _pos) => {
                LangVariable::Proper(proper.deref_proper_var().into())
            },
        }
    }

    pub fn pos(&self) -> Pos {
        match *self {
            Variable::CommonVar(_, _, pos) |
            Variable::ProperVar(_, pos) => {
                pos
            },
        }
    }
}

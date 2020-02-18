use std::fmt;
use lang_constructs::LangVariable;
use syntax::lexer::Token;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Pos(pub usize, pub usize);

#[derive(Debug)]
pub struct Statement<'a> {
    pub kind: StatementKind<'a>,
    pub pos: Pos,
}

#[derive(Debug)]
pub enum StatementKind<'a> {
    Assign(LValue<'a>, Expr<'a>),
    Incr(LValue<'a>, u32),
    Decr(LValue<'a>, u32),
    Say(Expr<'a>),

    Continue,
    Break,
    Return(Expr<'a>),

    Condition(Expr<'a>, Vec<Statement<'a>>, Vec<Statement<'a>>),
    While(Expr<'a>, Vec<Statement<'a>>),
    Until(Expr<'a>, Vec<Statement<'a>>),
    FuncDef(Variable<'a>, Vec<Variable<'a>>, Vec<Statement<'a>>),
}

#[derive(Debug)]
pub enum Expr<'a> {
    LValue(LValue<'a>),
    Literal(Token<'a>),
    Compare(Box<Comparison<'a>>),
    FuncCall(Box<Expr<'a>>, Vec<Box<Expr<'a>>>),

    Add(Box<Expr<'a>>, Box<Expr<'a>>),
    Sub(Box<Expr<'a>>, Box<Expr<'a>>),
    Mul(Box<Expr<'a>>, Box<Expr<'a>>),
    Div(Box<Expr<'a>>, Box<Expr<'a>>),

    Logical(Box<Logical<'a>>),
}

impl<'a> Expr<'a> {
    pub fn compare(comparison: Comparison<'a>) -> Self {
        Expr::Compare(Box::new(comparison))
    }

    pub fn logical(logical: Logical<'a>) -> Self {
        Expr::Logical(Box::new(logical))
    }
}

#[derive(Debug)]
pub struct Comparison<'a>(pub Expr<'a>, pub Comparator, pub Expr<'a>);

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
pub enum Logical<'a> {
    Not(Expr<'a>),
    And(Expr<'a>, Expr<'a>),
    Or(Expr<'a>, Expr<'a>),
    Nor(Expr<'a>, Expr<'a>),
}

pub enum LValue<'a> {
    Variable(Variable<'a>),
    Pronoun(Token<'a>),
}

impl<'a> fmt::Debug for LValue<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LValue::Variable(Variable::ProperVar(p, pos)) => write!(f, "ProperVar({} [{:?}])", p, pos),
            LValue::Variable(Variable::CommonVar(p, v, pos)) => write!(f, "CommonVar({} {}, [{:?}])", p, v, pos),
            LValue::Pronoun(p) => write!(f, "Pronoun({})", p),
        }
    }
}

#[derive(Debug)]
pub enum Variable<'a> {
    ProperVar(Token<'a>, Pos),
    CommonVar(Token<'a>, Token<'a>, Pos),
}

impl<'a> Variable<'a> {
    pub fn to_lang_variable<'b>(&'b self) -> LangVariable<'b> {
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

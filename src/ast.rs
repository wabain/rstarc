use std::fmt;
use lexer::Token;
use lang_constructs::LangVariable;

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct Pos(pub usize, pub usize);

#[derive(Debug)]
pub struct Statement {
    pub kind: StatementKind,
    pub pos: Pos,
}

#[derive(Debug)]
pub enum StatementKind {
    Assign(LValue, Expr),
    Incr(LValue),
    Decr(LValue),
    Say(Expr),

    Continue,
    Break,
    Return(Expr),

    Condition(Conditional, Vec<Statement>, Vec<Statement>),
    While(Conditional, Vec<Statement>),
    Until(Conditional, Vec<Statement>),
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
}

#[derive(Debug)]
pub enum Conditional {
    Comparison(Comparison),
    And(Box<Conditional>, Box<Conditional>),
    Or(Box<Conditional>, Box<Conditional>),
}

#[derive(Debug)]
pub struct Comparison(pub Expr, pub Comparator, pub Expr);

#[derive(Debug, Copy, Clone)]
pub enum Comparator {
    Is,
    IsNot,
    IsGreaterThan,
    IsLessThan,
    IsAsGreatAs,
    IsAsLittleAs,
}

pub enum LValue {
    Variable(Variable),
    Pronoun(Token),
}

impl fmt::Debug for LValue {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            LValue::Variable(Variable::ProperVar(p)) => write!(f, "ProperVar({})", p),
            LValue::Variable(Variable::CommonVar(p, v)) => write!(f, "CommonVar({} {})", p, v),
            LValue::Pronoun(p) => write!(f, "Pronoun({})", p),
        }
    }
}

#[derive(Debug)]
pub enum Variable {
    ProperVar(Token),
    CommonVar(Token, Token),
}

impl Variable {
    pub fn to_lang_variable<'a>(&'a self) -> LangVariable<'a> {
        match self {
            Variable::CommonVar(prep, common) => {
                LangVariable::Common(
                    prep.deref_common_prep().into(),
                    common.deref_common_var().into(),
                )
            },
            Variable::ProperVar(proper) => {
                LangVariable::Proper(proper.deref_proper_var().into())
            },
        }
    }
}

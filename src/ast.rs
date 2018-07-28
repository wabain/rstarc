use lexer::Token;

#[derive(Debug)]
pub enum Statement {
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

#[derive(Debug)]
pub enum LValue {
    Variable(Variable),
    Pronoun(Token),
}

#[derive(Debug)]
pub enum Variable {
    ProperVar(Token),
    CommonVar(Token, Token),
}

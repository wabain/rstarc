use std::fmt;
use std::mem;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::hash_map::{HashMap, Entry};

use lang_constructs::{Value, LangVariable};
use ast::{Statement, Expr, Conditional, Comparison, Comparator, LValue};

pub fn interpret(program: &[Statement]) -> () {
    Interpreter::default().run_program(program);
}

type InterpValue<'a> = Value<InterpFunc<'a>>;
type ScopeCell<'a> = Rc<RefCell<Scope<'a>>>;

#[derive(Clone)]
struct InterpFunc<'a> {
    id: u64,
    args: Vec<LangVariable<'a>>,
    statements: &'a [Statement],
    parent_scope: ScopeCell<'a>,
}

impl<'a> fmt::Debug for InterpFunc<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "InterpFunc #{}", self.id)
    }
}

impl<'a> PartialEq for InterpFunc<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

#[derive(Default, Debug)]
struct Scope<'a> {
    vars: HashMap<LangVariable<'a>, InterpValue<'a>>,
    parent: Option<ScopeCell<'a>>,
}

impl<'a> Scope<'a> {
    fn child(parent: ScopeCell<'a>) -> Scope<'a> {
        Scope {
            vars: HashMap::new(),
            parent: Some(parent),
        }
    }

    fn to_cell(self) -> ScopeCell<'a> {
        Rc::new(RefCell::new(self))
    }
}

#[derive(Debug)]
enum Flow<'a> {
    Next,
    Continue,
    Break,
    Return(InterpValue<'a>),
}

/// A simple interpreter that reads off the AST
#[derive(Default)]
pub struct Interpreter<'a> {
    func_id: u64,
    scope: ScopeCell<'a>,
}

impl<'a> Interpreter<'a> {
    fn run_program(mut self, program: &'a [Statement]) {
        self.dispatch_statements(program);
    }

    fn dispatch_statements(&mut self, statements: &'a [Statement]) -> Flow<'a> {
        for statement in statements {
            let flow = self.exec_statement(&statement);
            if let Flow::Next = flow {
                continue;
            }
            return flow;
        }
        Flow::Next
    }

    fn exec_statement(&mut self, statement: &'a Statement) -> Flow<'a> {
        match statement {
            Statement::Assign(lval, expr) => {
                let value = self.eval_expr(expr);
                let var = self.lval_to_var(lval);
                self.set_var(var, value);
            },
            Statement::Incr(lval) | Statement::Decr(lval) => {
                let var = self.lval_to_var(lval);
                let mut value = self.get_var(&var).coerce_number();
                match statement {
                    Statement::Incr(_) => value += 1.0,
                    Statement::Decr(_) => value -= 1.0,
                    _ => unreachable!(),
                }
                self.set_var(var, Value::Number(value));
            },
            Statement::Say(expr) => {
                let value = self.eval_expr(expr);
                println!("{}", value.user_display());
            }
            Statement::Continue => return Flow::Continue,
            Statement::Break => return Flow::Break,
            Statement::Return(expr) => {
                let value = self.eval_expr(expr);
                return Flow::Return(value);
            }
            Statement::Condition(cond, if_clause, else_clause) => {
                let flow = if self.eval_cond(cond) {
                    self.dispatch_statements(if_clause)
                } else {
                    self.dispatch_statements(else_clause)
                };
                return flow;
            },
            Statement::While(cond, clause) => {
                while self.eval_cond(cond) {
                    let flow = self.dispatch_statements(clause);
                    match flow {
                        Flow::Next | Flow::Continue => {},
                        Flow::Break => break,
                        Flow::Return(..) => return flow,
                    }
                }
            },
            Statement::Until(cond, clause) => {
                while !self.eval_cond(cond) {
                    let flow = self.dispatch_statements(clause);
                    match flow {
                        Flow::Next | Flow::Continue => {},
                        Flow::Break => break,
                        Flow::Return(..) => return flow,
                    }
                }
            },
            Statement::FuncDef(var, args, statements) => {
                let id = self.func_id;
                self.func_id += 1;

                let func = InterpFunc {
                    id,
                    args: args.iter().map(|a| a.to_lang_variable()).collect(),
                    statements,
                    parent_scope: self.scope.clone(),
                };

                self.set_var(var.to_lang_variable(), Value::Function(func));
            },
        }

        Flow::Next
    }

    fn eval_expr(&mut self, expr: &Expr) -> InterpValue<'a> {
        match expr {
            Expr::LValue(lval) => {
                let var = self.lval_to_var(lval);
                self.get_var(&var)
            },
            Expr::Literal(token) => {
                let value = token.literal_value().expect("take literal value");
                value
            },
            Expr::Compare(comp) => {
                let value = self.eval_comparison(comp);
                Value::Boolean(value)
            },
            Expr::FuncCall(func_expr, arg_exprs) => {
                let func_value = self.eval_expr(func_expr);

                let func = match func_value {
                    Value::Function(func) => func,
                    _ => {
                        // FIXME: Error handling?
                        return Value::Mysterious
                    }
                };

                let mut fcall_scope = Scope::child(func.parent_scope);

                let arg_values: Vec<_> = arg_exprs.iter()
                    .map(|a| self.eval_expr(a))
                    .collect();

                for (arg_var, arg_value) in func.args.iter().zip(arg_values.into_iter()) {
                    fcall_scope.vars.insert(arg_var.clone(), arg_value);
                }

                // Preset arguments for which values weren't provided by
                // the caller to shadow any values in parent scopes
                for i in arg_exprs.len()..func.args.len() {
                    fcall_scope.vars.insert(func.args[i].clone(), Value::Mysterious);
                }

                let flow;

                {
                    let mut old_scope = mem::replace(&mut self.scope,
                                                     fcall_scope.to_cell());

                    flow = self.dispatch_statements(func.statements);

                    mem::replace(&mut self.scope, old_scope);
                };

                match flow {
                    Flow::Return(value) => value,
                    Flow::Next => Value::Mysterious,
                    _ => unreachable!("{:?}", flow),
                }
            },
            Expr::Add(e1, e2) | Expr::Sub(e1, e2) | Expr::Mul(e1, e2) | Expr::Div(e1, e2) => {
                let n1 = self.eval_expr(e1).coerce_number();
                let n2 = self.eval_expr(e2).coerce_number();

                let value = match expr {
                    Expr::Add(..) => n1 + n2,
                    Expr::Sub(..) => n1 - n2,
                    Expr::Mul(..) => n1 * n2,
                    Expr::Div(..) => n1 / n2,
                    _ => unreachable!(),
                };

                Value::Number(value)
            },
        }
    }

    // FIXME: Why is this separate from expr anyway?
    // There are parsing differences, but not anything at the AST level?
    fn eval_cond(&mut self, cond: &Conditional) -> bool {
        match cond {
            Conditional::Comparison(comp) => self.eval_comparison(comp),
            Conditional::And(a, b) => self.eval_cond(a) && self.eval_cond(b),
            Conditional::Or(a, b) => self.eval_cond(a) || self.eval_cond(b),
        }
    }

    fn eval_comparison(&mut self, comparison: &Comparison) -> bool {
        let Comparison(ref e1, comp, ref e2) = *comparison;
        let mut v1 = self.eval_expr(e1);
        let mut v2 = self.eval_expr(e2);

        if v1.value_type() != v2.value_type() {
            v1 = Value::Number(v1.coerce_number());
            v2 = Value::Number(v2.coerce_number());
        }

        match comp {
            Comparator::Is => v1 == v2,
            Comparator::IsNot => v1 != v2,
            Comparator::IsGreaterThan => v1.coerce_number() > v2.coerce_number(),
            Comparator::IsLessThan => v1.coerce_number() < v2.coerce_number(),
            Comparator::IsAsGreatAs => v1.coerce_number() >= v2.coerce_number(),
            Comparator::IsAsLittleAs => v1.coerce_number() <= v2.coerce_number(),
        }
    }

    fn lval_to_var<'v>(&self, lval: &'v LValue) -> LangVariable<'v> {
        match lval {
            LValue::Pronoun(pronoun) => unimplemented!("pronoun {}", pronoun),
            LValue::Variable(var) => var.to_lang_variable(),
        }
    }

    fn get_var(&mut self, var: &LangVariable) -> InterpValue<'a> {
        // XXX: Seems awkward to have to incr/decr the refcount
        // just to read variables
        let mut scope_cell = Some(self.scope.clone());

        while let Some(sc) = scope_cell {
            let scope = sc.borrow();

            if let Some(value) = scope.vars.get(var) {
                return value.clone();
            }

            scope_cell = scope.parent.clone();
        }

        Value::Mysterious
    }

    // If the variable already exists in a parent scope, overwrite it.
    // Otherwise, write it to the leaf scope.
    fn set_var(&mut self, var: LangVariable<'a>, value: InterpValue<'a>) {
        let mut scope = Some(self.scope.clone());
        let mut var = var;

        while let Some(sc) = scope {
            match sc.borrow_mut().vars.entry(var) {
                Entry::Occupied(mut e) => {
                    e.insert(value);
                    return;
                }
                Entry::Vacant(e) => {
                    // Reacquire the the key
                    var = e.into_key()
                }
            }

            scope = sc.borrow_mut().parent.clone();
        }

        self.scope.borrow_mut().vars.insert(var, value);
    }
}

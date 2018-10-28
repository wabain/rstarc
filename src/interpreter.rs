use std::error;
use std::fmt;
use std::mem;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use std::cmp::Ordering;

use base_analysis;
use lang_constructs::{Value, LangVariable};
use ast::{Statement, StatementKind, Expr, Logical, Comparison, Comparator, LValue};
use runtime_error::RuntimeError;

pub fn interpret(program: &[Statement], scope_map: &base_analysis::ScopeMap)
    -> Result<(), RuntimeError>
{
    Interpreter::new(scope_map).run_program(program)?;
    Ok(())
}

#[derive(Debug)]
pub enum InterpreterError {
    NotAFunction { value_repr: String },
    IllegalOperands { op: &'static str, v1: String, v2: Option<String> },
}

impl InterpreterError {
    fn illegal_op<'a, 'b: 'a, O>(op: &'static str, v1: &InterpValue, v2: O) -> Self
        where O: Into<Option<&'a InterpValue<'b>>>
    {
        let v2 = v2.into();
        InterpreterError::IllegalOperands {
            op,
            v1: format!("{}", v1.user_display()),
            v2: v2.map(|v2| format!("{}", v2.user_display())),
        }
    }
}

impl error::Error for InterpreterError {}

impl fmt::Display for InterpreterError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InterpreterError::NotAFunction { value_repr } => {
                write!(f, "Cannot call value '{}'", value_repr)
            }
            InterpreterError::IllegalOperands { op, v1, v2 } => {
                if let Some(v2) = v2 {
                    write!(f, "Cannot {} {} and {}", op, v1, v2)
                } else {
                    write!(f, "Cannot {} {}", op, v1)
                }
            }
        }
    }
}

type InterpResult<T> = Result<T, InterpreterError>;

type InterpValue<'a> = Value<InterpFunc<'a>>;
type ScopeCell<'a> = Rc<RefCell<VariableScope<'a>>>;

#[derive(Clone)]
struct InterpFunc<'a> {
    id: u64,
    static_scope_id: base_analysis::ScopeId,
    args: Vec<LangVariable<'a>>,
    statements: &'a [Statement],
    parent_scope: ScopeCell<'a>,
}

impl<'a> fmt::Debug for InterpFunc<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "InterpFunc #{} (scope {})", self.id, self.static_scope_id)
    }
}

impl<'a> PartialEq for InterpFunc<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

#[derive(Default, Debug)]
struct VariableScope<'a> {
    static_scope_id: base_analysis::ScopeId,
    vars: HashMap<LangVariable<'a>, InterpValue<'a>>,
    parent: Option<ScopeCell<'a>>,
}

impl<'a> VariableScope<'a> {
    fn for_function(func: &InterpFunc<'a>) -> VariableScope<'a> {
        VariableScope {
            static_scope_id: func.static_scope_id,
            vars: HashMap::new(),
            parent: Some(func.parent_scope.clone()),
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
pub struct Interpreter<'a> {
    func_id: u64,
    scope: ScopeCell<'a>,
    scope_map: &'a base_analysis::ScopeMap<'a>,
}

impl<'a> Interpreter<'a> {
    fn new(scope_map: &'a base_analysis::ScopeMap<'a>) -> Self {
        Interpreter {
            func_id: 0,
            scope: ScopeCell::default(),
            scope_map,
        }
    }

    fn run_program(mut self, program: &'a [Statement]) -> InterpResult<()>
    {
        self.dispatch_statements(program)?;
        Ok(())
    }

    fn dispatch_statements(&mut self, statements: &'a [Statement])
        -> InterpResult<Flow<'a>>
    {
        for statement in statements {
            let flow = self.exec_statement(statement)?;
            if let Flow::Next = flow {
                continue;
            }
            return Ok(flow);
        }
        Ok(Flow::Next)
    }

    fn exec_statement(&mut self, statement: &'a Statement)
        -> InterpResult<Flow<'a>>
    {
        match &statement.kind {
            StatementKind::Assign(lval, expr) => {
                let value = self.eval_expr(expr)?;
                let var = self.lval_to_var(lval);
                self.set_var(var, value);
            },
            StatementKind::Incr(lval) | StatementKind::Decr(lval) => {
                let var = self.lval_to_var(lval);

                let new_var = match self.get_var(&var) {
                    Value::Number(n) => match statement.kind {
                        StatementKind::Incr(_) => Value::Number(n + 1.),
                        StatementKind::Decr(_) => Value::Number(n - 1.),
                        _ => unreachable!(),
                    }
                    Value::Boolean(b) => Value::Boolean(!b),
                    v @ _ => {
                        let op = match statement.kind {
                            StatementKind::Incr(_) => "increment",
                            StatementKind::Decr(_) => "decrement",
                            _ => unreachable!(),
                        };
                        return Err(InterpreterError::illegal_op(op, &v, None));
                    }
                };

                self.set_var(var, new_var);
            },
            StatementKind::Say(expr) => {
                let value = self.eval_expr(expr)?;
                println!("{}", value.user_display());
            }
            StatementKind::Continue => return Ok(Flow::Continue),
            StatementKind::Break => return Ok(Flow::Break),
            StatementKind::Return(expr) => {
                let value = self.eval_expr(expr)?;
                return Ok(Flow::Return(value));
            }
            StatementKind::Condition(cond, if_clause, else_clause) => {
                let flow = if self.eval_cond(cond)? {
                    self.dispatch_statements(if_clause)?
                } else {
                    self.dispatch_statements(else_clause)?
                };
                return Ok(flow);
            },
            StatementKind::While(cond, clause) => {
                while self.eval_cond(cond)? {
                    let flow = self.dispatch_statements(clause)?;
                    match flow {
                        Flow::Next | Flow::Continue => {},
                        Flow::Break => break,
                        Flow::Return(..) => return Ok(flow),
                    }
                }
            },
            StatementKind::Until(cond, clause) => {
                while !self.eval_cond(cond)? {
                    let flow = self.dispatch_statements(clause)?;
                    match flow {
                        Flow::Next | Flow::Continue => {},
                        Flow::Break => break,
                        Flow::Return(..) => return Ok(flow),
                    }
                }
            },
            StatementKind::FuncDef(var, args, statements) => {
                let id = self.func_id;
                self.func_id += 1;

                let func = InterpFunc {
                    id,
                    static_scope_id: self.scope_map.get_scope_for_func_declaration(statement),
                    args: args.iter().map(|a| a.to_lang_variable()).collect(),
                    statements,
                    parent_scope: self.scope.clone(),
                };

                self.set_var(var.to_lang_variable(), Value::Function(func));
            },
        }

        Ok(Flow::Next)
    }

    fn eval_expr(&mut self, expr: &Expr) -> InterpResult<InterpValue<'a>> {
        let value = match expr {
            Expr::LValue(lval) => {
                let var = self.lval_to_var(lval);
                self.get_var(&var)
            },
            Expr::Literal(token) => {
                let value = token.literal_value().expect("take literal value");
                value
            },
            Expr::Compare(comp) => {
                let value = self.eval_comparison(comp)?;
                Value::Boolean(value)
            },
            Expr::FuncCall(func_expr, arg_exprs) => {
                let func_value = self.eval_expr(func_expr)?;
                self.exec_func_call(func_value, arg_exprs)?
            },
            Expr::Add(e1, e2) | Expr::Sub(e1, e2) | Expr::Mul(e1, e2) | Expr::Div(e1, e2) => {
                let v1 = self.eval_expr(e1)?;
                let v2 = self.eval_expr(e2)?;
                self.eval_binary_op(expr, v1, v2)?
            },
            Expr::Logical(logical) => {
                match logical.as_ref() {
                    Logical::And(e1, e2) => {
                        let v1 = self.eval_expr(e1)?;
                        if v1.coerce_boolean() {
                            self.eval_expr(e2)?
                        } else {
                            v1
                        }
                    }
                    Logical::Or(e1, e2) => {
                        let v1 = self.eval_expr(e1)?;
                        if v1.coerce_boolean() {
                            v1
                        } else {
                            self.eval_expr(e2)?
                        }
                    }
                }
            }
        };
        Ok(value)
    }

    fn exec_func_call(&mut self,
                      func_value: InterpValue<'a>,
                      arg_exprs: &[Box<Expr>])
        -> InterpResult<InterpValue<'a>>
    {
        let func = match func_value {
            Value::Function(func) => func,
            _ => {
                return Err(InterpreterError::NotAFunction {
                    value_repr: format!("{}", func_value.user_display()),
                });
            }
        };

        let mut fcall_scope = VariableScope::for_function(&func);

        let arg_values = {
            let mut v = Vec::with_capacity(arg_exprs.len());
            for a in arg_exprs {
                v.push(self.eval_expr(a)?);
            }
            v
        };

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
            let old_scope = mem::replace(&mut self.scope, fcall_scope.to_cell());
            let res = self.dispatch_statements(func.statements);
            mem::replace(&mut self.scope, old_scope);

            flow = res?;
        };

        match flow {
            Flow::Return(value) => Ok(value),
            Flow::Next => Ok(Value::Mysterious),
            _ => unreachable!("{:?}", flow),
        }
    }

    fn eval_binary_op(&self, expr: &Expr, v1: InterpValue, v2: InterpValue)
        -> InterpResult<InterpValue<'a>>
    {
        let value = match (expr, &v1, &v2) {
            (_, &Value::Number(n1), &Value::Number(n2)) => {
                let out = match expr {
                    Expr::Add(..) => n1 + n2,
                    Expr::Sub(..) => n1 - n2,
                    Expr::Mul(..) => n1 * n2,
                    Expr::Div(..) => n1 / n2,
                    _ => unreachable!(),
                };
                Value::Number(out)
            }

            (Expr::Add(..), Value::String(_), _) |
            (Expr::Add(..), _, Value::String(_)) => {
                match (v1.coerce_string(), v2.coerce_string()) {
                    (Some(s1), Some(s2)) => {
                        let size = s1.as_bytes().len() + s2.as_bytes().len();
                        let mut combined = String::with_capacity(size);
                        combined.push_str(&s1);
                        combined.push_str(&s2);
                        Value::String(combined)
                    }
                    _ => return Err(InterpreterError::illegal_op("add", &v1, &v2)),
                }
            }

            (Expr::Mul(..), &Value::Number(n), Value::String(s)) |
            (Expr::Mul(..), Value::String(s), &Value::Number(n)) => {
                if n.is_nan() || n < 0. {
                    return Err(InterpreterError::illegal_op("multiply", &v1, &v2));
                }
                let n = n.trunc() as usize;
                Value::String(s.repeat(n))
            }

            _ => {
                let op = match expr {
                    Expr::Add(..) => "add",
                    Expr::Sub(..) => "subtract",
                    Expr::Mul(..) => "multiply",
                    Expr::Div(..) => "divide",
                    _ => unreachable!(),
                };
                return Err(InterpreterError::illegal_op(op, &v1, &v2))
            }
        };
        Ok(value)
    }

    fn eval_cond(&mut self, cond: &Expr) -> InterpResult<bool> {
        let val = self.eval_expr(cond)?;
        Ok(val.coerce_boolean())
    }

    fn eval_comparison(&mut self, comparison: &Comparison) -> InterpResult<bool> {
        let Comparison(ref e1, comp, ref e2) = *comparison;
        let v1 = self.eval_expr(e1)?;
        let v2 = self.eval_expr(e2)?;

        let (v1, v2) = match Value::coerce_binary_operands(v1, v2) {
            Some(pair) => pair,
            None => {
                return Ok(comp == Comparator::IsNot)
            }
        };

        debug_assert_eq!(v1.value_type(), v2.value_type());

        match comp {
            Comparator::Is => return Ok(v1 == v2),
            Comparator::IsNot => return Ok(v1 != v2),
            _ => {}
        }

        let ordering = match (&v1, &v2) {
            (Value::String(s1), Value::String(s2)) => s1.partial_cmp(s2),
            (Value::Number(n1), Value::Number(n2)) => n1.partial_cmp(n2),
            (Value::Boolean(b1), Value::Boolean(b2)) => b1.partial_cmp(b2),
            (Value::Function(_), Value::Function(_)) => None,
            (Value::Null, Value::Null) |
            (Value::Mysterious, Value::Mysterious) => Some(Ordering::Equal),
            (_, _) => unreachable!("values {:?} {:?}", v1, v2),
        };

        let compared = match comp {
            Comparator::Is | Comparator::IsNot => unreachable!(),
            Comparator::IsGreaterThan => ordering == Some(Ordering::Greater),
            Comparator::IsLessThan => ordering == Some(Ordering::Less),
            Comparator::IsAsGreatAs => {
                ordering.is_some() && ordering != Some(Ordering::Less)
            }
            Comparator::IsAsLittleAs => {
                ordering.is_some() && ordering != Some(Ordering::Greater)
            }
        };

        Ok(compared)
    }

    fn lval_to_var<'v>(&self, lval: &'v LValue) -> LangVariable<'v> {
        match lval {
            LValue::Pronoun(pronoun) => unimplemented!("pronoun {}", pronoun),
            LValue::Variable(var) => var.to_lang_variable(),
        }
    }

    fn get_var(&mut self, var: &LangVariable) -> InterpValue<'a> {
        let scope = self.scope.borrow();
        let leaf_scope_id = scope.static_scope_id;
        let owning_scope_id = if let Some(own) = self.scope_map
                .get_owning_scope_for_var(&var, leaf_scope_id)
        {
            own
        } else {
            // Values can be missing from the owning scope map if they were never
            // written
            return Value::Mysterious;
        };

        // Fast path: local read, don't need to touch refcounts
        if owning_scope_id == leaf_scope_id {
            // FIXME: Do I really need to clone?
            return scope.vars.get(var).map_or(Value::Mysterious, Value::clone);
        }

        // Slow path: walk the scope chain to find the owning scope
        let scope_cell = self.find_ancestor_scope_by_id(owning_scope_id);
        let value = scope_cell.borrow().vars
            .get(var)
            .map_or(Value::Mysterious, Value::clone);

        value
    }

    // If the variable already exists in a parent scope, overwrite it.
    // Otherwise, write it to the leaf scope.
    fn set_var(&mut self, var: LangVariable<'a>, value: InterpValue<'a>) {
        let leaf_scope_id = self.scope.borrow().static_scope_id;
        let owning_scope_id = self.scope_map
            .get_owning_scope_for_var(&var, leaf_scope_id)
            .unwrap_or_else(|| {
                panic!("No known owning scope on write for {:?} from scope {}",
                       var, leaf_scope_id)
            });

        // Fast path: local write, don't need to touch refcounts
        if owning_scope_id == leaf_scope_id {
            self.scope.borrow_mut().vars.insert(var, value);
            return;
        }

        // Slow path: walk the scope chain to find the owning scope
        let scope_cell = self.find_ancestor_scope_by_id(owning_scope_id);
        scope_cell.borrow_mut().vars.insert(var, value);
    }

    fn find_ancestor_scope_by_id(&self, static_id: base_analysis::ScopeId) -> ScopeCell<'a> {
        // Slow path: walk the scope chain to find the owning scope
        let mut scope_cell = self.scope.borrow().parent.clone();

        while let Some(sc) = scope_cell {
            if sc.borrow().static_scope_id == static_id {
                return sc;
            }

            scope_cell = sc.borrow().parent.clone();
        }

        panic!("Did not find scope {} from {:?}", static_id, self.scope);
    }
}

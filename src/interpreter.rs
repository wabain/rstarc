use std::error;
use std::fmt;
use std::iter;
use std::mem;
use std::rc::Rc;
use std::cell::RefCell;
use std::collections::HashMap;
use std::borrow::Cow;

use smallvec::SmallVec;

use rstarc_types::Value;
use base_analysis::{ScopeId, ScopeMap, VariableType};
use lang_constructs::{RockstarValue as BaseValue, LangVariable};
use runtime_error::RuntimeError;
use syntax::ast::{
    Statement,
    StatementKind,
    Expr,
    Logical,
    Comparison,
    Comparator,
    LValue,
};

pub fn interpret<'prog>(program: &[Statement], scope_map: &ScopeMap<'prog>)
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

type InterpValue<'a> = BaseValue<'a, InterpFunc<'a>>;
type ValueCell<'a> = Rc<RefCell<InterpValue<'a>>>;
type ScopeCell<'a> = Rc<RefCell<VariableScope<'a>>>;

#[derive(Clone)]
struct InterpFunc<'a> {
    id: u64,
    static_scope_id: ScopeId,
    args: Vec<LangVariable<'a>>,
    statements: &'a [Statement<'a>],
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

#[derive(Debug)]
struct VariableScope<'a> {
    static_scope_id: ScopeId,
    local: Vec<InterpValue<'a>>,
    closure: Vec<ValueCell<'a>>,
}

impl<'a> VariableScope<'a> {
    fn new(layout: &VariableLayout<'a>,
           static_scope_id: ScopeId,
           parent: Option<&VariableScope<'a>>)
        -> Self
    {
        let scope_layout = &layout.scope_layouts[static_scope_id as usize];
        let local = init_var_lookup(scope_layout.locals_count);
        let closure = scope_layout.closure_srcs.iter().map(|src| {
            match *src {
                ClosureSrc::Local => Rc::new(RefCell::new(Value::Mysterious)),
                ClosureSrc::Parent(idx) => {
                    Rc::clone(&parent
                        .expect("closure scope parent")
                        .closure[idx])
                }
            }
        }).collect();

        VariableScope {
            static_scope_id,
            local,
            closure,
        }
    }

    fn for_root(layout: &VariableLayout<'a>) -> Self {
        VariableScope::new(layout, 0, None)
    }

    fn for_function(layout: &VariableLayout<'a>, func: &InterpFunc<'a>) -> Self {
        VariableScope::new(layout,
                           func.static_scope_id,
                           Some(&func.parent_scope.borrow()))
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
pub struct Interpreter<'a, 'prog> {
    func_id: u64,
    scope: ScopeCell<'a>,
    scope_map: &'a ScopeMap<'prog>,
    globals: Vec<InterpValue<'a>>,
    var_layout: VariableLayout<'a>,
}

impl<'a, 'prog> Interpreter<'a, 'prog> {
    fn new(scope_map: &'a ScopeMap<'prog>) -> Self {
        let var_layout = VariableLayout::new(scope_map);
        Interpreter {
            func_id: 0,
            scope: VariableScope::for_root(&var_layout).to_cell(),
            scope_map,
            globals: init_var_lookup(var_layout.globals_count),
            var_layout,
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
            StatementKind::Incr(lval, count) | StatementKind::Decr(lval, count) => {
                let var = self.lval_to_var(lval);
                let count = *count;

                let new_var = match self.get_var(&var) {
                    Value::Number(n) => match statement.kind {
                        StatementKind::Incr(..) => Value::Number(n + (count as f64)),
                        StatementKind::Decr(..) => Value::Number(n - (count as f64)),
                        _ => unreachable!(),
                    }
                    Value::Boolean(b) => {
                        if count % 2 == 1 {
                            Value::Boolean(!b)
                        } else {
                            Value::Boolean(b)
                        }
                    }
                    v @ _ => {
                        let op = match statement.kind {
                            StatementKind::Incr(..) => "increment",
                            StatementKind::Decr(..) => "decrement",
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
                    parent_scope: Rc::clone(&self.scope),
                };

                self.set_var(var.to_lang_variable(), Value::Function(func));
            },
        }

        Ok(Flow::Next)
    }

    fn eval_expr(&mut self, expr: &'a Expr<'a>) -> InterpResult<InterpValue<'a>> {
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
                    Logical::Not(e) => {
                        let v = self.eval_expr(e)?;
                        let value = !v.coerce_boolean();
                        Value::Boolean(value)
                    }
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
                    Logical::Nor(e1, e2) => {
                        let v1 = self.eval_expr(e1)?;
                        if v1.coerce_boolean() {
                            Value::Boolean(false)
                        } else {
                            let v2 = self.eval_expr(e2)?;
                            Value::Boolean(!v2.coerce_boolean())
                        }
                    }
                }
            }
        };
        Ok(value)
    }

    fn exec_func_call(&mut self,
                      func_value: InterpValue<'a>,
                      arg_exprs: &'a [Expr<'a>])
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

        let fcall_scope = self.init_function_scope(&func, arg_exprs)?;
        let flow = {
            let old_scope = mem::replace(&mut self.scope, fcall_scope.to_cell());
            let res = self.dispatch_statements(func.statements);
            mem::replace(&mut self.scope, old_scope);

            res?
        };

        match flow {
            Flow::Return(value) => Ok(value),
            Flow::Next => Ok(Value::Mysterious),
            _ => unreachable!("{:?}", flow),
        }
    }

    fn eval_binary_op(&self, expr: &'a Expr<'a>, v1: InterpValue, v2: InterpValue)
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
                        Value::String(Rc::new(Cow::Owned(combined)))
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
                Value::String(Rc::new(Cow::Owned(s.repeat(n))))
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

    fn eval_cond(&mut self, cond: &'a Expr<'a>) -> InterpResult<bool> {
        let val = self.eval_expr(cond)?;
        Ok(val.coerce_boolean())
    }

    fn eval_comparison(&mut self, comparison: &'a Comparison<'a>) -> InterpResult<bool> {
        let Comparison(ref e1, comp, ref e2) = *comparison;
        let v1 = self.eval_expr(e1)?;
        let v2 = self.eval_expr(e2)?;

        let compared = match comp {
            Comparator::Is => v1.rstar_is(v2),
            Comparator::IsNot => v1.rstar_is_not(v2),
            Comparator::IsGreaterThan => v1.rstar_gt(v2),
            Comparator::IsLessThan => v1.rstar_lt(v2),
            Comparator::IsAsGreatAs => v1.rstar_ge(v2),
            Comparator::IsAsLittleAs => v1.rstar_le(v2),
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
        let scope_id = scope.static_scope_id;

        match *self.var_layout.get_storage_type(scope_id, var) {
            StorageType::Global(idx) => self.globals[idx].clone(),
            StorageType::Local(idx) => scope.local[idx].clone(),
            StorageType::Closure(idx) => scope.closure[idx].borrow().clone(),
        }
    }

    // If the variable already exists in a parent scope, overwrite it.
    // Otherwise, write it to the leaf scope.
    fn set_var(&mut self, var: LangVariable<'a>, value: InterpValue<'a>) {
        let mut scope = self.scope.borrow_mut();
        let scope_id = scope.static_scope_id;

        match *self.var_layout.get_storage_type(scope_id, &var) {
            StorageType::Global(idx) => { self.globals[idx] = value; }
            StorageType::Local(idx) => { scope.local[idx] = value; }
            StorageType::Closure(idx) => { *scope.closure[idx].borrow_mut() = value; }
        }
    }

    fn init_function_scope(&mut self,
                           func: &InterpFunc<'a>,
                           arg_exprs: &'a [Expr<'a>])
        -> InterpResult<VariableScope<'a>>
    {
        let scope_id = func.static_scope_id;
        let mut fcall_scope = VariableScope::for_function(&self.var_layout, func);

        // Evaluate arguments and assign them in a child scope. Need to
        // maintain predictable evaluation order here.
        for (arg_expr, var) in arg_exprs.iter().zip(func.args.iter()) {
            let value = self.eval_expr(arg_expr)?;

            match *self.var_layout.get_storage_type(scope_id, var) {
                StorageType::Global(_) => panic!("Cannot assign function argument as global"),
                StorageType::Local(idx) => {
                    fcall_scope.local[idx] = value;
                }
                StorageType::Closure(idx) => {
                    *fcall_scope.closure[idx].borrow_mut() = value;
                }
            }
        }

        Ok(fcall_scope)
    }
}

type VariableIndexLookup<'prog> = HashMap<&'prog LangVariable<'prog>, usize>;

struct VariableLayout<'prog> {
    globals_count: usize,
    scope_layouts: Vec<ScopeLayout<'prog>>,
}

impl<'prog> VariableLayout<'prog> {
    fn new(scope_map: &'prog ScopeMap) -> Self {
        let mut globals = HashMap::new();

        let mut scope_layouts: Vec<_> =
            scope_map.scopes().map(|_| ScopeLayout::default()).collect();
        let mut closures: Vec<_> =
            scope_map.scopes().map(|_| HashMap::new()).collect();

        for scope_id in scope_map.scopes() {
            for (var, var_type) in scope_map.get_used_vars_for_scope(scope_id) {
                match var_type {
                    VariableType::Closure(owner) => {
                        VariableLayout::register_closure_var(
                            scope_map,
                            scope_id,
                            owner,
                            var,
                            &mut closures,
                            &mut scope_layouts,
                        );
                    }
                    VariableType::Global => {
                        let globals_count = globals.len();
                        let idx = *globals.entry(var).or_insert(globals_count);
                        let layout = &mut scope_layouts[scope_id as usize];
                        layout.register_global_var(var, idx);
                    }
                    VariableType::Local(_) => {
                        let layout = &mut scope_layouts[scope_id as usize];
                        layout.register_local_var(var);
                    }
                }
            }
        }

        VariableLayout {
            globals_count: globals.len(),
            scope_layouts,
        }
    }

    /// Register a closure variable. For a non-local closure access, the
    /// variable must be registered in each scope between the accessing scope
    /// and the owner.
    fn register_closure_var(
        scope_map: &'prog ScopeMap,
        scope_id: ScopeId,
        owner: ScopeId,
        var: &'prog LangVariable<'prog>,
        closures: &mut [VariableIndexLookup<'prog>],
        scope_layouts: &mut [ScopeLayout<'prog>],
    ) {
        if owner == scope_id {
            let layout = &mut scope_layouts[scope_id as usize];
            let idx = layout.register_closure_var(var, ClosureSrc::Local);
            closures[scope_id as usize].insert(var, idx);
            return;
        }

        let resolution_chain: SmallVec<[ScopeId; 4]> =
            iter::once(scope_id)
            .chain(scope_map
                .get_ancestor_scopes(scope_id)
                .take_while(|&s| s != owner))
            .collect();

        for required in resolution_chain.into_iter().rev() {
            let (prior_closures, next_closures) = closures.split_at_mut(required as usize);

            next_closures[0].entry(var).or_insert_with(|| {
                let parent_id = scope_map.get_parent_scope(required)
                    .expect("Parent of scope with closure");

                let parent_idx = prior_closures[parent_id as usize][var];

                let layout = &mut scope_layouts[required as usize];
                layout.register_closure_var(var, ClosureSrc::Parent(parent_idx))
            });
        }
    }

    fn get_storage_type<'a>(&'a self, scope_id: ScopeId, var: &'a LangVariable)
        -> &'a StorageType
    {
        self.scope_layouts[scope_id as usize]
            .vars.get(var)
            .expect("variable layout lookup")
    }
}

#[derive(Debug)]
enum StorageType {
    Global(usize),
    Local(usize),
    Closure(usize),
}

#[derive(Debug, Copy, Clone)]
enum ClosureSrc {
    Local,
    Parent(usize),
}

#[derive(Default, Debug)]
struct ScopeLayout<'prog> {
    vars: HashMap<&'prog LangVariable<'prog>, StorageType>,
    locals_count: usize,
    closure_srcs: Vec<ClosureSrc>,
}

impl<'prog> ScopeLayout<'prog> {
    fn register_global_var(&mut self, var: &'prog LangVariable<'prog>, idx: usize) -> usize {
        self.vars.insert(var, StorageType::Global(idx));
        idx
    }

    fn register_local_var(&mut self, var: &'prog LangVariable<'prog>) -> usize {
        let idx = self.locals_count;
        self.locals_count += 1;

        self.vars.insert(var, StorageType::Local(idx));

        idx
    }

    fn register_closure_var(&mut self, var: &'prog LangVariable<'prog>, src: ClosureSrc) -> usize {
        let idx = self.closure_srcs.len();
        self.closure_srcs.push(src);

        self.vars.insert(var, StorageType::Closure(idx));

        idx
    }
}

fn init_var_lookup<'a>(size: usize) -> Vec<InterpValue<'a>> {
    vec![Value::Mysterious; size]
}

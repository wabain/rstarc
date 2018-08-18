use std::fmt;
use std::borrow::Cow;
use std::collections::HashSet;

use base_analysis::{ScopeId, ScopeMap, VariableType};
use ast::{self, Expr, Conditional, Statement, StatementKind, Pos};
use lang_constructs::{self, LangVariable};

use base_analysis::CompileError;

pub fn build_ir<'prog>(program: &'prog [Statement],
                       scope_map: &'prog ScopeMap<'prog>)
                       -> Result<IRProgram<'prog>, CompileError>
{
    AstAdapter::adapt(program, scope_map)
}

pub fn dump_ir(program: &[Statement], scope_map: &ScopeMap)
    -> Result<(), CompileError>
{
    let ir = AstAdapter::adapt(program, scope_map)?;

    for (global_var, var_scope) in &ir.globals {
        println!("global {}<{}>", global_var, var_scope);
    }

    if ir.globals.len() > 0 {
        println!();
    }

    println!("main:");
    for op in &ir.main {
        dump_ir_op(0, op);
    }

    for (func_def, func_body) in &ir.funcs {
        println!("");

        println!(";");
        print!("; Function {} takes ", func_def.initial_var);
        for (i, arg) in func_def.args.iter().enumerate() {
            if i == 0 {
                print!("{}", arg.fmt_scope_relative(func_def.scope_id));
            } else {
                print!(", {}", arg.fmt_scope_relative(func_def.scope_id));
            }
        }
        println!("");
        println!("; Scope is {}", func_def.scope_id);
        println!(";");

        let fname = format!("{}", func_def.initial_var).replace(" ", "_");
        println!("f{}_{}:", func_def.scope_id, fname);

        for op in func_body {
            dump_ir_op(func_def.scope_id, op);
        }
    }

    Ok(())
}

fn dump_ir_op(scope_id: ScopeId, op: &SimpleIR) {
    macro_rules! fmt_scoped {
        ($v:expr) => {
            $v.fmt_scope_relative(scope_id)
        };
    }

    match op {
        SimpleIR::Jump(label) => println!("  jump .{}", label.name()),

        SimpleIR::JumpIf(cond, then_label, else_label) => {
            println!("  jumpif {}, .{}, .{}", cond, then_label.name(), else_label.name());
        }

        SimpleIR::Label(label) => println!(".{}:", label.name()),

        SimpleIR::Operate(op, dst, arg1, arg2) => {
            let op_fmt = match op {
                BinOp::Compare(ast::Comparator::Is) => "is",
                BinOp::Compare(ast::Comparator::IsNot) => "is-not",
                BinOp::Compare(ast::Comparator::IsGreaterThan) => "gt",
                BinOp::Compare(ast::Comparator::IsLessThan) => "lt",
                BinOp::Compare(ast::Comparator::IsAsGreatAs) => "ge",
                BinOp::Compare(ast::Comparator::IsAsLittleAs) => "le",
                BinOp::Add => "add",
                BinOp::Sub => "sub",
                BinOp::Mul => "mul",
                BinOp::Div => "div",
            };
            println!("  {} := {} {}, {}",
                     fmt_scoped!(dst),
                     op_fmt,
                     fmt_scoped!(arg1),
                     fmt_scoped!(arg2));
        }

        SimpleIR::LoadArg(dst, idx) => {
            println!("  {} := load-arg {}", fmt_scoped!(dst), idx);
        }

        SimpleIR::Store(dst, arg) => {
            println!("  {} := store {}", fmt_scoped!(dst), fmt_scoped!(arg));
        }

        SimpleIR::Call(dst, func, args) => {
            print!("  {} := call {}, [", fmt_scoped!(dst), fmt_scoped!(func));
            for (i, arg) in args.iter().enumerate() {
                if i == 0 {
                    print!("{}", fmt_scoped!(arg));
                } else {
                    print!(", {}", fmt_scoped!(arg));
                }
            }
            println!("]");
        }

        SimpleIR::Say(arg) => {
            println!("  say {}", fmt_scoped!(arg));
        }

        SimpleIR::Return(arg) => {
            println!("  return {}", fmt_scoped!(arg));
        }

        SimpleIR::ReturnDefault => {
            println!("  return-default");
        }
    }
}

/// Run some basic sanity checks on the IR.
///
/// Currently this verifies that temporaries are (trivially) in SSA form,
/// and that no unsupported cross-scope reads occur.
fn verify_ir_func<'a>(scope_map: &ScopeMap,
                      scope_id: ScopeId,
                      ops: &'a[SimpleIR])
    -> Result<(), CompileError>
{
    let mut vals_seen: HashSet<&'a IRLValue> = HashSet::new();

    let handle_value = |v: &IRValue| -> Result<(), CompileError> {
        match v {
            IRValue::Variable(var, i, p) if *i != scope_id => {
                let var_type = scope_map.get_scope_data(*i)
                    .get_variable_type(var)
                    .expect("get variable in owner");

                if var_type == VariableType::Closure {
                    Err(CompileError::UnsupportedFeature {
                        feature: format!("using non-local variable '{}'", var),
                        has_interpreter_support: true,
                        pos: Some(*p),
                    })
                } else {
                    Ok(())
                }
            }
            _ => Ok(())
        }
    };

    let handle_write = |vals_seen: &mut HashSet<_>, v: &'a IRLValue|
        -> Result<(), CompileError>
    {
        match v {
            IRLValue::LocalTemp(_) => {
                if vals_seen.contains(&v) {
                    panic!("Multiple writes to {}", &v);
                }
                vals_seen.insert(v);
            }
            IRLValue::Variable(..) => {
                vals_seen.insert(v);
                handle_value(&v.clone().into())?;
            }
        }
        Ok(())
    };

    for op in ops {
        match op {
            // Branching ops
            SimpleIR::JumpIf(v, _, _) => {
                handle_value(v)?;
            }
            SimpleIR::Jump(..) |
            SimpleIR::Label(..) => {}

            // Write ops
            SimpleIR::Operate(_, lval, v1, v2) => {
                handle_write(&mut vals_seen, lval)?;
                handle_value(v1)?;
                handle_value(v2)?;
            }
            SimpleIR::LoadArg(lval, _) => {
                handle_write(&mut vals_seen, lval)?;
            }
            SimpleIR::Store(lval, v) => {
                handle_write(&mut vals_seen, lval)?;
                handle_value(v)?;
            }
            SimpleIR::Call(lval, v, args) => {
                handle_write(&mut vals_seen, lval)?;
                handle_value(v)?;
                for a in args {
                    handle_value(a)?;
                }
            }

            // Other no-write ops
            SimpleIR::Say(v) |
            SimpleIR::Return(v) => {
                handle_value(v)?;
            }
            SimpleIR::ReturnDefault => {}
        }
    }

    Ok(())
}

#[derive(Debug, Copy, Clone)]
pub struct Label {
    id: u64,
    name_hint: &'static str,
}

impl Label {
    pub fn name(&self) -> String {
        format!("{}{}", self.name_hint, self.id)
    }
}

type LiteralValue = lang_constructs::Value<ScopeId>;

#[derive(Debug, Hash, PartialEq, Eq, Copy, Clone)]
pub struct LocalTemp(u64);

impl fmt::Display for LocalTemp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "t{}", self.0)
    }
}

#[derive(Debug, Clone)]
pub enum IRValue<'prog> {
    Literal(LiteralValue),
    LocalTemp(LocalTemp),
    Variable(LangVariable<'prog>, ScopeId, Pos),
}

impl<'prog> IRValue<'prog> {
    fn fmt_scope_relative<'a>(&'a self, ref_scope: ScopeId) -> IRValuePrinter<'a> {
        IRValuePrinter {
            ir_value: Cow::Borrowed(&self),
            ref_scope: Some(ref_scope),
        }
    }
}

impl<'prog> fmt::Display for IRValue<'prog> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        IRValuePrinter {
            ir_value: Cow::Borrowed(self),
            ref_scope: None,
        }.fmt(f)
    }
}

struct IRValuePrinter<'a> {
    ir_value: Cow<'a, IRValue<'a>>,
    ref_scope: Option<ScopeId>,
}

impl<'a> fmt::Display for IRValuePrinter<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.ir_value.as_ref() {
            IRValue::Literal(lit) => write!(f, "{}", lit.repr_format()),
            IRValue::LocalTemp(t) => write!(f, "{}", t),
            IRValue::Variable(v, i, _pos) => {
                let is_local = self.ref_scope.map_or(false, |r| r == *i);
                if is_local {
                    write!(f, "{}", v)
                } else {
                    write!(f, "{}<{}>", v, i)
                }
            }
        }
    }
}

#[derive(Debug, Hash, PartialEq, Eq, Clone)]
pub enum IRLValue<'prog> {
    LocalTemp(LocalTemp),
    Variable(LangVariable<'prog>, ScopeId, Pos),
}

impl<'prog> IRLValue<'prog> {
    fn fmt_scope_relative(&self, scope_id: ScopeId) -> IRValuePrinter {
        let val = self.clone().into();
        IRValuePrinter {
            ir_value: Cow::Owned(val),
            ref_scope: Some(scope_id),
        }
    }
}

impl<'prog> fmt::Display for IRLValue<'prog> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let val: IRValue = self.clone().into();
        write!(f, "{}", val)
    }
}

impl<'prog> Into<IRValue<'prog>> for IRLValue<'prog> {
    fn into(self) -> IRValue<'prog> {
        match self {
            IRLValue::LocalTemp(t) => IRValue::LocalTemp(t),
            IRLValue::Variable(v, i, p) => IRValue::Variable(v, i, p),
        }
    }
}

pub struct IRProgram<'prog> {
    pub scope_map: &'prog ScopeMap<'prog>,
    pub globals: Vec<(LangVariable<'prog>, ScopeId)>,
    pub main: Vec<SimpleIR<'prog>>,
    pub funcs: Vec<(IRFunc<'prog>, Vec<SimpleIR<'prog>>)>,
}

#[derive(Debug)]
pub struct IRFunc<'prog> {
    pub scope_id: ScopeId,
    pub initial_var: LangVariable<'prog>,
    pub args: Vec<IRLValue<'prog>>,
}

#[derive(Debug, Copy, Clone)]
pub enum BinOp {
    Compare(ast::Comparator),
    Add,
    Sub,
    Mul,
    Div,
}

/// Simple intermediate representation. This is just a flattened
/// version of the source AST, with control flow translated to jumps.
#[derive(Debug)]
pub enum SimpleIR<'prog> {
    Jump(Label),
    JumpIf(IRValue<'prog>, Label, Label),
    Label(Label),
    LoadArg(IRLValue<'prog>, usize),
    Operate(BinOp, IRLValue<'prog>, IRValue<'prog>, IRValue<'prog>),
    Store(IRLValue<'prog>, IRValue<'prog>),
    Call(IRLValue<'prog>, IRValue<'prog>, Vec<IRValue<'prog>>),
    Say(IRValue<'prog>),
    Return(IRValue<'prog>),
    ReturnDefault,
}

impl<'prog> SimpleIR<'prog> {
    pub fn is_terminator(&self) -> bool {
        match self {
            SimpleIR::Jump(..) |
            SimpleIR::JumpIf(..) |
            SimpleIR::Return(..) |
            SimpleIR::ReturnDefault => true,

            SimpleIR::Label(..) |
            SimpleIR::LoadArg(..) |
            SimpleIR::Operate(..) |
            SimpleIR::Store(..) |
            SimpleIR::Call(..) |
            SimpleIR::Say(..) => false,
        }
    }
}

struct IRBuilder<'prog> {
    scope_map: &'prog ScopeMap<'prog>,
    ref_scope: ScopeId,
    label_id: u64,
    temp_id: u64,
    ops: Vec<SimpleIR<'prog>>,
    loop_labels: Vec<[Label; 2]>,
}

impl<'prog> IRBuilder<'prog> {
    fn new(scope_map: &'prog ScopeMap<'prog>, ref_scope: ScopeId) -> Self {
        IRBuilder {
            scope_map,
            ref_scope,
            label_id: 0,
            temp_id: 0,
            ops: Vec::new(),
            loop_labels: Vec::new(),
        }
    }

    // XXX inline this?
    fn lookup_scope(&self, var: &LangVariable) -> ScopeId {
        self.scope_map.get_owning_scope_for_var(var, self.ref_scope)
            .expect("variable scope lookup")
    }

    fn resolve_ast_variable(&self, var: &'prog ast::Variable) -> IRLValue<'prog> {
        let lang_var = var.to_lang_variable();
        let scope_id = self.lookup_scope(&lang_var);
        IRLValue::Variable(lang_var, scope_id, var.pos())
    }

    fn synthesize_ir_lval(&self, var: &LangVariable<'prog>, pos: Pos)
        -> IRLValue<'prog>
    {
        let scope_id = self.lookup_scope(var);
        IRLValue::Variable(var.clone(), scope_id, pos)
    }

    fn emit(&mut self, ir_entry: SimpleIR<'prog>) {
        let is_block_end = self.ops.last()
            .map_or(false, |o| o.is_terminator());

        let mut insert_new_entry = true;

        if let SimpleIR::Label(label) = ir_entry {
            // Insert a jump when falling through to a label
            if !is_block_end {
                self.ops.push(SimpleIR::Jump(label));
            }
        } else if is_block_end {
            // This operation will be unreachable. If it is one which is
            // auto-generated, we can silently drop it without complicating
            // the control flow. If it's user-originated, we'll insert it.
            //
            // TODO(wabain): Figure out how to lint on unreachable code.
            // Presumably it's possible to do this and other linting after
            // lowering to LLVM. But if that's too hard, just walk the Simple
            // IR and find the blocks emitted below.
            match ir_entry {
                SimpleIR::Jump(..) |
                SimpleIR::JumpIf(..) |
                SimpleIR::ReturnDefault => { insert_new_entry = false; }
                _ => {
                    let unreachable_label = self.label("unreachable");
                    self.ops.push(SimpleIR::Label(unreachable_label));
                }
            }
        }

        if insert_new_entry {
            self.ops.push(ir_entry);
        }
    }

    fn enter_loop(&mut self, labels: [Label; 2]) {
        self.loop_labels.push(labels);
    }

    fn exit_loop(&mut self) {
        self.loop_labels.pop().expect("IRBuilder::exit_loop");
    }

    fn loop_start(&self) -> Option<Label> {
        self.loop_labels.last().map(|ls| ls[0])
    }

    fn loop_end(&self) -> Option<Label> {
        self.loop_labels.last().map(|ls| ls[1])
    }

    fn temp(&mut self) -> IRLValue<'prog> {
        let id = self.temp_id;
        self.temp_id += 1;
        IRLValue::LocalTemp(LocalTemp(id))
    }

    fn label(&mut self, name_hint: &'static str) -> Label {
        let id = self.label_id;
        self.label_id += 1;
        Label { id, name_hint }
    }

    fn emit_label(&mut self, label: Label) {
        self.emit(SimpleIR::Label(label));
    }

    fn emit_expr(&mut self, dst: Option<IRLValue<'prog>>, expr: &'prog ast::Expr)
        -> IRValue<'prog>
    {
        match expr {
            Expr::LValue(lval) => {
                let var = resolve_ast_lval(lval);
                let ir_val = self.resolve_ast_variable(var).into();

                if let Some(ir_lval) = dst {
                    self.emit(SimpleIR::Store(
                        ir_lval.clone(),
                        ir_val,
                    ));

                    ir_lval.into()
                } else {
                    ir_val
                }
            }
            Expr::Literal(tok) => {
                let value = tok.literal_value().expect("take literal value");
                let value = IRValue::Literal(value);

                if let Some(dst) = dst {
                    self.emit(SimpleIR::Store(
                        dst.clone(),
                        value,
                    ));
                    dst.into()
                } else {
                    value
                }
            }
            Expr::Compare(comp) => self.emit_comparison(dst, comp).into(),
            Expr::FuncCall(func, args) => {
                let f_var = self.emit_expr(None, func);
                let args = args.iter()
                    .map(|arg_expr| self.emit_expr(None, arg_expr).into())
                    .collect();

                let dst = dst.unwrap_or_else(|| self.temp());

                self.emit(SimpleIR::Call(
                    dst.clone(),
                    f_var.into(),
                    args,
                ));

                dst.into()
            }

            Expr::Add(e1, e2) |
            Expr::Sub(e1, e2) |
            Expr::Mul(e1, e2) |
            Expr::Div(e1, e2) => {
                let a1 = self.emit_expr(None, e1);
                let a2 = self.emit_expr(None, e2);

                let op = match expr {
                    Expr::Add(..) => BinOp::Add,
                    Expr::Sub(..) => BinOp::Sub,
                    Expr::Mul(..) => BinOp::Mul,
                    Expr::Div(..) => BinOp::Div,
                    _ => unreachable!(),
                };

                let dst = dst.unwrap_or_else(|| self.temp());

                self.emit(SimpleIR::Operate(
                    op,
                    dst.clone(),
                    a1.into(),
                    a2.into(),
                ));

                dst.into()
            }
        }
    }

    fn emit_cond(&mut self,
                 cond: &'prog ast::Conditional,
                 then_label: Label,
                 else_label: Label)
    {
        match cond {
            Conditional::Comparison(comp) => {
                let dst = self.emit_comparison(None, comp);
                self.emit(SimpleIR::JumpIf(dst.into(), then_label, else_label));
            }
            Conditional::And(c1, c2) => {
                let and_label = self.label("and");

                self.emit_cond(c1, and_label, else_label);

                self.emit_label(and_label);
                self.emit_cond(c2, then_label, else_label);
            }
            Conditional::Or(c1, c2) => {
                let or_label = self.label("or");

                self.emit_cond(c1, then_label, or_label);

                self.emit_label(or_label);
                self.emit_cond(c2, then_label, else_label);
            }
        }
    }

    fn emit_comparison(&mut self,
                       dst: Option<IRLValue<'prog>>,
                       comp: &'prog ast::Comparison)
        -> IRLValue<'prog>
    {
        let ast::Comparison(ref e1, comp, ref e2) = *comp;
        let a1 = self.emit_expr(None, e1);
        let a2 = self.emit_expr(None, e2);

        let dst = dst.unwrap_or_else(|| self.temp());
        self.emit(SimpleIR::Operate(
            BinOp::Compare(comp),
            dst.clone(),
            a1.into(),
            a2.into(),
        ));
        dst
    }

    fn emit_scope_initializers(&mut self,
                               globals: &mut Vec<(LangVariable<'prog>, ScopeId)>,
                               func_pos: Pos,
                               args: &[IRLValue<'prog>])
    {
        fn unwrap_variable<'a>(ir_lval: &'a IRLValue) -> &'a LangVariable<'a> {
            match ir_lval {
                IRLValue::Variable(v, ..) => v,
                _ => unreachable!("looking only at lang variables, got \
                                    {:?}", ir_lval)
            }
        };

        let scope_data = self.scope_map.get_scope_data(self.ref_scope);

        for var in self.scope_map.get_owned_vars_for_scope(self.ref_scope) {
            if let Some((idx, arg)) = args.iter().enumerate().find(|(_, v)| {
                unwrap_variable(*v) == var
            }) {
                self.emit(SimpleIR::LoadArg(arg.clone(), idx));
            } else if scope_data.get_variable_type(var) == Some(VariableType::Global) {
                let scope_id = self.lookup_scope(var);
                globals.push((var.clone(), scope_id));
            } else {
                let ir_lval = self.synthesize_ir_lval(var, func_pos);
                let initial_value = IRValue::Literal(lang_constructs::Value::Mysterious);
                self.emit(SimpleIR::Store(ir_lval, initial_value));
            }
        }
    }
}

/// This is the first pass to lowering the AST to assembly.
/// Here we simply unroll block statements and split up the separate
/// functions to be generated.
struct AstAdapter<'prog> {
    scope_map: &'prog ScopeMap<'prog>,
    globals: Vec<(LangVariable<'prog>, ScopeId)>,
    func_bodies: Vec<(IRFunc<'prog>, Vec<SimpleIR<'prog>>)>,
}

impl<'prog> AstAdapter<'prog> {
    fn adapt(program: &'prog [Statement], scope_map: &'prog ScopeMap<'prog>)
        -> Result<IRProgram<'prog>, CompileError>
    {
        let mut adapter = AstAdapter {
            scope_map,
            globals: Vec::new(),
            func_bodies: Vec::new(),
        };

        let mut main_builder = IRBuilder::new(scope_map, 0);

        // Use the start of the program file as the position for initializers
        // in main
        adapter.visit_function_body(&mut main_builder, Pos(0, 0), &[], program);

        verify_ir_func(scope_map, 0, &main_builder.ops)?;
        for (func_def, body) in &adapter.func_bodies {
            verify_ir_func(scope_map, func_def.scope_id, body)?;
        }

        Ok(IRProgram {
            scope_map,
            globals: adapter.globals,
            main: main_builder.ops,
            funcs: adapter.func_bodies,
        })
    }

    fn visit_function_body(&mut self,
                           ir_builder: &mut IRBuilder<'prog>,
                           func_pos: Pos,
                           args: &[IRLValue<'prog>],
                           statements: &'prog [Statement])
    {
        ir_builder.emit_scope_initializers(&mut self.globals, func_pos, args);
        self.visit_statements(ir_builder, statements);

        if !ir_builder.ops.last().map_or(false, |o| o.is_terminator()) {
            ir_builder.emit(SimpleIR::ReturnDefault);
        }
    }

    fn visit_statements(&mut self, ir_builder: &mut IRBuilder<'prog>, statements: &'prog [Statement]) {
        for statement in statements {
            self.visit_statement(ir_builder, statement);
        }
    }

    fn visit_statement(&mut self, ir_builder: &mut IRBuilder<'prog>, statement: &'prog Statement) {
        match &statement.kind {
            StatementKind::Assign(lval, expr) => {
                let var = resolve_ast_lval(lval);
                let ir_lval = ir_builder.resolve_ast_variable(var);
                ir_builder.emit_expr(Some(ir_lval), expr);
            }
            StatementKind::Incr(lval) | StatementKind::Decr(lval) => {
                let var = resolve_ast_lval(lval);
                let ir_lval = ir_builder.resolve_ast_variable(var);

                let add_val = match &statement.kind {
                    StatementKind::Incr(..) =>
                        IRValue::Literal(lang_constructs::Value::Number(1.0)),
                    StatementKind::Decr(..) =>
                        IRValue::Literal(lang_constructs::Value::Number(-1.0)),
                    _ => unreachable!(),
                };

                ir_builder.emit(SimpleIR::Operate(BinOp::Add,
                                                  ir_lval.clone(),
                                                  ir_lval.into(),
                                                  add_val));
            }
            StatementKind::Say(expr) => {
                let expr_var = ir_builder.emit_expr(None, expr).into();
                ir_builder.emit(SimpleIR::Say(expr_var));
            }

            StatementKind::Continue => {
                let start_label = ir_builder.loop_start().expect("AstAdapter: Continue label");
                ir_builder.emit(SimpleIR::Jump(start_label));
            }
            StatementKind::Break => {
                let end_label = ir_builder.loop_end().expect("AstAdapter: Break label");
                ir_builder.emit(SimpleIR::Jump(end_label));
            }
            StatementKind::Return(expr) => {
                let expr_var = ir_builder.emit_expr(None, expr).into();
                ir_builder.emit(SimpleIR::Return(expr_var))
            }

            StatementKind::While(cond, body) => {
                self.handle_loop(ir_builder, cond, true, body);
            }
            StatementKind::Until(cond, body) => {
                self.handle_loop(ir_builder, cond, false, body);
            }
            StatementKind::Condition(cond, if_block, else_block) => {
                let if_label = ir_builder.label("then");
                let else_label = ir_builder.label("else");

                let if_end_label = if else_block.is_empty() {
                    None
                } else {
                    Some(ir_builder.label("if_end"))
                };

                ir_builder.emit_cond(cond, if_label, else_label);

                ir_builder.emit_label(if_label);
                self.visit_statements(ir_builder, if_block);

                if let Some(end_label) = if_end_label {
                    ir_builder.emit(SimpleIR::Jump(end_label));
                }

                ir_builder.emit_label(else_label);
                self.visit_statements(ir_builder, else_block);

                if let Some(end_label) = if_end_label {
                    ir_builder.emit_label(end_label);
                }
            }
            StatementKind::FuncDef(var, args, body) => {
                let scope_id = self.scope_map.get_scope_for_func_declaration(statement);

                let initial_var = var.to_lang_variable();
                let args: Vec<_> = args.iter().map(|v| {
                    IRLValue::Variable(v.to_lang_variable(), scope_id, v.pos())
                }).collect();

                let ir_lval = ir_builder.resolve_ast_variable(&var);
                ir_builder.emit(SimpleIR::Store(
                    ir_lval,
                    IRValue::Literal(lang_constructs::Value::Function(scope_id)),
                ));

                let mut func_builder = IRBuilder::new(self.scope_map, scope_id);
                self.visit_function_body(&mut func_builder, statement.pos, &args, body);

                let func_def = IRFunc { initial_var, scope_id, args };

                self.func_bodies.push((func_def, func_builder.ops));
            }
        }
    }

    fn handle_loop(&mut self,
                   ir_builder: &mut IRBuilder<'prog>,
                   cond: &'prog Conditional,
                   loop_while_true: bool,
                   body: &'prog [Statement])
    {
        let check_label = ir_builder.label("loop_check");
        let start_label = ir_builder.label("loop_start");
        let end_label = ir_builder.label("loop_end");

        ir_builder.emit_label(check_label);

        if loop_while_true {
            ir_builder.emit_cond(cond, start_label, end_label);
        } else {
            ir_builder.emit_cond(cond, end_label, start_label);
        }

        ir_builder.emit_label(start_label);
        ir_builder.enter_loop([check_label, end_label]);
        self.visit_statements(ir_builder, body);
        ir_builder.exit_loop();

        ir_builder.emit(SimpleIR::Jump(check_label));
        ir_builder.emit_label(end_label);
    }
}

fn resolve_ast_lval<'prog>(lval: &'prog ast::LValue) -> &'prog ast::Variable {
    match lval {
        ast::LValue::Pronoun(..) => unreachable!(),
        ast::LValue::Variable(var) => var,
    }
}

#[cfg(test)]
mod test {
    use lang_constructs::Value;
    use super::{verify_ir_func, SimpleIR, IRValue, IRLValue, LocalTemp};

    #[test]
    #[should_panic]
    fn verify_ir_double_write_temporary() {
        let scope_map = Default::default();
        verify_ir_func(&scope_map, 0, &[
            SimpleIR::Store(
                IRLValue::LocalTemp(LocalTemp(1)),
                IRValue::Literal(Value::Mysterious),
            ),
            SimpleIR::Store(
                IRLValue::LocalTemp(LocalTemp(1)),
                IRValue::Literal(Value::Null),
            ),
        ]).unwrap()
    }
}

use std::fmt;

use base_analysis::{ScopeId, ScopeMap};
use ast::{self, Expr, Conditional, Statement, StatementKind};
use lang_constructs::{self, LangVariable};

pub fn dump_ir(program: &[Statement], scope_map: &ScopeMap) {
    let ir = AstAdapter::adapt(program, scope_map);

    println!("main:");
    for op in &ir.main {
        dump_ir_op(op);
    }

    for (func_def, func_body) in &ir.funcs {
        println!("");

        println!(";");
        print!("; Function {} takes ", func_def.initial_var);
        for (i, arg) in func_def.args.iter().enumerate() {
            if i == 0 {
                print!("{}", arg);
            } else {
                print!(", {}", arg);
            }
        }
        println!("");
        println!(";");

        let fname = format!("{}", func_def.initial_var).replace(" ", "_");
        println!("f{}_{}:", func_def.scope_id, fname);

        for op in func_body {
            dump_ir_op(op);
        }
    }
}

fn dump_ir_op(op: &SimpleIR) {
    match op {
        SimpleIR::Jump(label) => println!("  jump .{}{}", label.name_hint, label.id),

        SimpleIR::JumpIf(label, jump_type, cond) => {
            let type_fmt = match jump_type {
                JumpType::If => "if",
                JumpType::IfNot => "unless",
            };
            println!("  jump{} {}, .{}{}", type_fmt, cond, label.name_hint, label.id);
        }

        SimpleIR::Label(label) => println!(".{}{}:", label.name_hint, label.id),

        SimpleIR::Operate(op, dst, arg1, arg2) => {
            let op_fmt = match op {
                BinOp::Compare(ast::Comparator::Is) => "is",
                BinOp::Compare(ast::Comparator::IsNot) => "is-not",
                BinOp::Compare(ast::Comparator::IsGreaterThan) => "is-gt",
                BinOp::Compare(ast::Comparator::IsLessThan) => "is-lt",
                BinOp::Compare(ast::Comparator::IsAsGreatAs) => "is-ge",
                BinOp::Compare(ast::Comparator::IsAsLittleAs) => "is-le",
                BinOp::Add => "add",
                BinOp::Sub => "sub",
                BinOp::Mul => "mul",
                BinOp::Div => "div",
                BinOp::And => "and",
                BinOp::Or => "or",
            };
            println!("  {} := {} {}, {}", dst, op_fmt, arg1, arg2);
        }

        SimpleIR::Store(dst, arg) => {
            println!("  {} := store {}", dst, arg);
        }

        SimpleIR::Call(dst, func, args) => {
            print!("  {} := call {}, [", dst, func);
            for (i, arg) in args.iter().enumerate() {
                if i == 0 {
                    print!("{}", arg);
                } else {
                    print!(", {}", arg);
                }
            }
            println!("]");
        }

        SimpleIR::Say(arg) => {
            println!("  say {}", arg);
        }

        SimpleIR::Return(arg) => {
            println!("  return {}", arg);
        }
    }
}

#[derive(Debug, Copy, Clone)]
struct Label {
    id: u64,
    name_hint: &'static str,
}

type LiteralValue = lang_constructs::Value<ScopeId>;

#[derive(Debug, Copy, Clone)]
struct LocalTemp(u64);

#[derive(Debug)]
enum IRValue<'prog> {
    Literal(LiteralValue),
    LocalTemp(LocalTemp),
    Variable(LangVariable<'prog>),
}

impl<'prog> fmt::Display for IRValue<'prog> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            IRValue::Literal(lit) => write!(f, "{}", lit.repr_format()),
            IRValue::LocalTemp(t) => write!(f, "t{}", t.0),
            IRValue::Variable(v) => write!(f, "{}", v),
        }
    }
}

#[derive(Debug, Clone)]
enum IRLValue<'prog> {
    LocalTemp(LocalTemp),
    Variable(LangVariable<'prog>),
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
            IRLValue::Variable(v) => IRValue::Variable(v),
        }
    }
}

#[derive(Debug)]
struct IRProgram<'prog> {
    main: Vec<SimpleIR<'prog>>,
    funcs: Vec<(IRFunc<'prog>, Vec<SimpleIR<'prog>>)>,
}

#[derive(Debug)]
struct IRFunc<'prog> {
    scope_id: ScopeId,
    initial_var: LangVariable<'prog>,
    args: Vec<LangVariable<'prog>>,
}

#[derive(Debug, Copy, Clone)]
enum JumpType {
    If,
    IfNot
}

impl JumpType {
    fn flip(&self) -> JumpType {
        match self {
            JumpType::If => JumpType::IfNot,
            JumpType::IfNot => JumpType::If,
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum BinOp {
    Compare(ast::Comparator),
    Add,
    Sub,
    Mul,
    Div,
    And,
    Or,
}

/// Simple intermediate representation. This is just a flattened
/// version of the source AST, with control flow translated to jumps.
#[derive(Debug)]
enum SimpleIR<'prog> {
    Jump(Label),
    JumpIf(Label, JumpType, IRValue<'prog>),
    Label(Label),
    Operate(BinOp, IRLValue<'prog>, IRValue<'prog>, IRValue<'prog>),
    Store(IRLValue<'prog>, IRValue<'prog>),
    Call(IRLValue<'prog>, IRValue<'prog>, Vec<IRValue<'prog>>),
    Say(IRValue<'prog>),
    Return(IRValue<'prog>),
}

#[derive(Default)]
struct IRBuilder<'prog> {
    temp_id: u64,
    ops: Vec<SimpleIR<'prog>>,
    loop_labels: Vec<[Label; 2]>,
}

impl<'prog> IRBuilder<'prog> {
    fn emit(&mut self, ir_entry: SimpleIR<'prog>) {
        self.ops.push(ir_entry);
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

    fn emit_expr(&mut self, dst: Option<IRLValue<'prog>>, expr: &'prog ast::Expr)
        -> IRValue<'prog>
    {
        match expr {
            Expr::LValue(lval) => {
                let var = resolve_lval(lval);

                if let Some(ir_lval) = dst {
                    self.emit(SimpleIR::Store(
                        ir_lval.clone(),
                        IRValue::Variable(var)
                    ));

                    ir_lval.into()
                } else {
                    IRValue::Variable(var)
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

    fn emit_cond(&mut self, dst: Option<IRLValue<'prog>>, cond: &'prog ast::Conditional)
        -> IRLValue<'prog>
    {
        use ast::Conditional;

        match cond {
            Conditional::Comparison(comp) => self.emit_comparison(dst, comp),
            Conditional::And(c1, c2) => {
                let a1 = self.emit_cond(None, c1);
                let a2 = self.emit_cond(None, c2);
                let dst = dst.unwrap_or_else(|| self.temp());
                self.emit(SimpleIR::Operate(
                    BinOp::And,
                    dst.clone(),
                    a1.into(),
                    a2.into(),
                ));
                dst
            }
            Conditional::Or(c1, c2) => {
                let a1 = self.emit_cond(None, c1);
                let a2 = self.emit_cond(None, c2);
                let dst = dst.unwrap_or_else(|| self.temp());
                self.emit(SimpleIR::Operate(
                    BinOp::Or,
                    dst.clone(),
                    a1.into(),
                    a2.into(),
                ));
                dst
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
}

/// This is the first pass to lowering the AST to assembly.
/// Here we simply unroll block statements and split up the separate
/// functions to be generated.
struct AstAdapter<'prog> {
    label_id: u64,
    scope_map: &'prog ScopeMap<'prog>,
    func_bodies: Vec<(IRFunc<'prog>, Vec<SimpleIR<'prog>>)>,
}

impl<'prog> AstAdapter<'prog> {
    fn adapt(program: &'prog [Statement], scope_map: &'prog ScopeMap<'prog>) -> IRProgram<'prog> {
        let mut adapter = AstAdapter {
            label_id: 0,
            scope_map,
            func_bodies: Vec::new(),
        };

        let mut main_builder = IRBuilder::default();
        adapter.visit_statements(&mut main_builder, program);

        IRProgram {
            main: main_builder.ops,
            funcs: adapter.func_bodies,
        }
    }

    fn label(&mut self, name_hint: &'static str) -> Label {
        let id = self.label_id;
        self.label_id += 1;
        Label { id, name_hint }
    }

    fn visit_statements(&mut self, ir_builder: &mut IRBuilder<'prog>, statements: &'prog [Statement]) {
        for statement in statements {
            self.visit_statement(ir_builder, statement);
        }
    }

    fn visit_statement(&mut self, ir_builder: &mut IRBuilder<'prog>, statement: &'prog Statement) {
        match &statement.kind {
            StatementKind::Assign(lval, expr) => {
                let var = resolve_lval(lval);
                ir_builder.emit_expr(Some(IRLValue::Variable(var)), expr);
            }
            StatementKind::Incr(lval) | StatementKind::Decr(lval) => {
                let var = resolve_lval(lval);

                let add_val = match &statement.kind {
                    StatementKind::Incr(..) =>
                        IRValue::Literal(lang_constructs::Value::Number(1.0)),
                    StatementKind::Decr(..) =>
                        IRValue::Literal(lang_constructs::Value::Number(-1.0)),
                    _ => unreachable!(),
                };

                ir_builder.emit(SimpleIR::Operate(BinOp::Add,
                                                  IRLValue::Variable(var.clone()),
                                                  IRValue::Variable(var),
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
                self.handle_loop(ir_builder, cond, JumpType::If, body);
            }
            StatementKind::Until(cond, body) => {
                self.handle_loop(ir_builder, cond, JumpType::IfNot, body);
            }
            StatementKind::Condition(cond, if_block, else_block) => {
                let else_label = self.label("else");

                let else_end_label = if else_block.is_empty() {
                    None
                } else {
                    Some(self.label("else_end"))
                };

                let ir_cond = ir_builder.emit_cond(None, cond);
                ir_builder.emit(SimpleIR::JumpIf(
                    else_label,
                    JumpType::IfNot,
                    ir_cond.into(),
                ));

                self.visit_statements(ir_builder, if_block);

                if let Some(end_label) = else_end_label {
                    ir_builder.emit(SimpleIR::Jump(end_label));
                }

                ir_builder.emit(SimpleIR::Label(else_label));
                self.visit_statements(ir_builder, else_block);

                if let Some(end_label) = else_end_label {
                    ir_builder.emit(SimpleIR::Label(end_label));
                }
            }
            StatementKind::FuncDef(var, args, body) => {
                let initial_var = var.to_lang_variable();
                let scope_id = self.scope_map.get_scope_for_func_declaration(statement);

                ir_builder.emit(SimpleIR::Store(
                    IRLValue::Variable(initial_var.clone()),
                    IRValue::Literal(lang_constructs::Value::Function(scope_id)),
                ));

                let mut func_builder = IRBuilder::default();
                self.visit_statements(&mut func_builder, body);

                let func_def = IRFunc {
                    initial_var,
                    scope_id,
                    args: args.iter().map(|v| v.to_lang_variable()).collect(),
                };

                self.func_bodies.push((func_def, func_builder.ops));
            }
        }
    }

    fn handle_loop(&mut self,
                   ir_builder: &mut IRBuilder<'prog>,
                   cond: &'prog Conditional,
                   jump_type: JumpType,
                   body: &'prog [Statement])
    {
        let start_label = self.label("loop_start");
        let end_label = self.label("loop_end");

        ir_builder.emit(SimpleIR::Label(start_label));

        let ir_cond = ir_builder.emit_cond(None, cond);
        ir_builder.emit(SimpleIR::JumpIf(
            end_label,
            jump_type.flip(),
            ir_cond.into(),
        ));

        ir_builder.enter_loop([start_label, end_label]);
        self.visit_statements(ir_builder, body);
        ir_builder.exit_loop();

        ir_builder.emit(SimpleIR::Jump(start_label));
        ir_builder.emit(SimpleIR::Label(end_label));
    }
}

fn resolve_lval<'prog>(lval: &'prog ast::LValue) -> LangVariable<'prog> {
    match lval {
        ast::LValue::Pronoun(..) => unreachable!(),
        ast::LValue::Variable(var) => var.to_lang_variable(),
    }
}

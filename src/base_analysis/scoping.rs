use std::collections::BTreeMap;
use std::collections::hash_map::{HashMap, Entry};

use syntax::ast::{self, Statement, StatementKind, LValue};
use lang_constructs::LangVariable;

pub type ScopeId = u64;
pub type SrcPos = usize;

/// A collector does a pass over the AST and notes all the variables
/// assigned and read to in different scopes.
pub fn identify_variable_scopes(program: &[Statement]) -> ScopeMap {
    let mut builder = ScopeMapBuilder::new();
    builder.walk_tree(program);
    builder.to_scope_map()
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum VariableType {
    /// Global variable. For now this must belong to the root scope, although
    /// it should be possible to use globals instead of closures in some cases.
    Global,
    Local(ScopeId),
    Closure(ScopeId),
}

impl VariableType {
    pub fn owner(&self) -> ScopeId {
        match *self {
            VariableType::Global => 0,
            VariableType::Local(s) | VariableType::Closure(s) => s,
        }
    }

    pub fn is_global(&self) -> bool {
        match self {
            VariableType::Global => true,
            _ => false,
        }
    }

    pub fn is_closure(&self) -> bool {
        match self {
            VariableType::Closure(_) => true,
            _ => false,
        }
    }

    fn register_use(&mut self, scope_id: ScopeId) {
        if let VariableType::Local(s) = *self {
            if s != scope_id {
                if s == 0 {
                    *self = VariableType::Global;
                } else {
                    *self = VariableType::Closure(s);
                }
            }
        }
    }
}

#[derive(Debug, PartialEq, Copy, Clone)]
enum UseType {
    Read,
    Write,
    ForcedLocalWrite,
}

impl UseType {
    fn merge(&mut self, other: UseType) {
        match (&self, other) {
            (UseType::Read, _) |
            (UseType::Write, UseType::ForcedLocalWrite) => { *self = other; }

            (_, UseType::Read) |
            (UseType::Write, UseType::Write) |
            (UseType::ForcedLocalWrite, _) => {}
        }
    }
}

#[derive(Default, Debug, Clone)]
struct ScopeData<'prog> {
    /// Id of this scope's parent
    parent_id: Option<ScopeId>,

    // Use a binary tree to get a stable iteration order. Ideally we'd
    // probably use insertion order, but that would also push extra
    // requirements into the the scope analysis pass.
    used_variables: BTreeMap<LangVariable<'prog>, VariableType>,
}

#[derive(Default)]
pub struct ScopeMap<'prog> {
    block_scopes: HashMap<SrcPos, ScopeId>,
    scope_data: Vec<ScopeData<'prog>>
}

impl<'prog> ScopeMap<'prog> {
    pub fn scopes(&self) -> impl Iterator<Item=ScopeId> {
        (0..self.scope_data.len() as ScopeId)
    }

    pub fn get_parent_scope(&self, scope_id: ScopeId) -> Option<ScopeId> {
        self.scope_data(scope_id).parent_id
    }

    pub fn get_scope_for_func_declaration(&self, statement: &Statement) -> ScopeId {
        *self.block_scopes.get(&statement.pos.0)
            .unwrap_or_else(|| panic!("No scope for statement {:?}", statement))
    }

    pub fn get_variable_type(&self,
                             var: &LangVariable,
                             referencing_scope: ScopeId) -> Option<VariableType>
    {
        self.scope_data(referencing_scope)
            .used_variables.get(var)
            .cloned()
    }

    pub fn get_used_vars_for_scope(&self, scope_id: ScopeId)
        -> impl Iterator<Item=(&LangVariable<'prog>, VariableType)>
    {
        self.scope_data(scope_id)
            .used_variables.iter()
            .map(|(k, &t)| (k, t))
    }

    pub fn get_owned_vars_for_scope(&self, scope_id: ScopeId)
        -> impl Iterator<Item=(&LangVariable<'prog>, VariableType)>
    {
        self.scope_data(scope_id)
            .used_variables.iter()
            .filter(move |(_, &t)| t.owner() == scope_id)
            .map(|(k, &t)| (k, t))
    }

    fn scope_data(&self, scope_id: ScopeId) -> &ScopeData<'prog> {
        self.scope_data.get(scope_id as usize).unwrap_or_else(|| {
            panic!("Missing scope data for scope {}", scope_id)
        })
    }
}

#[derive(Default)]
struct ScopeMapBuilder<'prog> {
    current_scope: ScopeId,
    scope_stack: Vec<ScopeId>,
    scope_parents: Vec<Option<ScopeId>>,
    block_scopes: HashMap<SrcPos, ScopeId>,
    var_uses: HashMap<LangVariable<'prog>, HashMap<ScopeId, UseType>>,
}

impl<'prog> ScopeMapBuilder<'prog> {
    fn new() -> Self {
        ScopeMapBuilder {
            scope_parents: vec![None],
            ..Self::default()
        }
    }

    fn to_scope_map(self) -> ScopeMap<'prog> {
        let mut scope_data: Vec<ScopeData> = self.scope_parents.iter()
            .map(|&parent_id| ScopeData { parent_id, ..Default::default() })
            .collect();

        for (var, var_users) in self.var_uses {
            let owner_for_scope = ScopeMapBuilder::analyze_use(&self.scope_parents, var_users);

            for (scope, var_type) in owner_for_scope {
                scope_data.get_mut(scope as usize)
                    .expect("scope data update")
                    .used_variables.insert(var.clone(), var_type);
            }
        }

        ScopeMap {
            block_scopes: self.block_scopes,
            scope_data,
        }
    }

    fn analyze_use(scope_parents: &[Option<ScopeId>],
                   var_users: HashMap<ScopeId, UseType>)
        -> HashMap<ScopeId, VariableType>
    {
        let mut var_instances = vec![];
        let mut owner_for_scope: HashMap<ScopeId, usize> = HashMap::with_capacity(var_users.len());

        let mut used_scopes: Vec<_> = var_users.keys().cloned().collect();
        used_scopes.sort();

        let first_scope_with_var = used_scopes[0];

        for scope_id in used_scopes {
            let mut var_inst = None;

            if var_users[&scope_id] != UseType::ForcedLocalWrite {
                let mut current_scope = scope_id;

                while current_scope > first_scope_with_var {
                    current_scope = match scope_parents[current_scope as usize] {
                        Some(s) => s,
                        None => break,
                    };

                    if let Some(&inst) = owner_for_scope.get(&current_scope) {
                        var_inst = Some(inst);
                        break;
                    }
                }
            }

            let var_inst = match var_inst {
                None => {
                    let idx = var_instances.len();
                    var_instances.push(VariableType::Local(scope_id));
                    idx
                }
                Some(idx) => {
                    var_instances[idx].register_use(scope_id);
                    idx
                }
            };

            owner_for_scope.insert(scope_id, var_inst);
        }

        owner_for_scope.into_iter()
            .map(|(s, i)| (s, var_instances[i]))
            .collect()
    }

    fn walk_tree(&mut self, tree: &'prog [Statement]) {
        for statement in tree {
            match &statement.kind {
                StatementKind::Assign(lval, e) => {
                    self.observe_expr(e);

                    let var = lval_to_lang_var(lval);
                    self.register_variable(var, UseType::Write);
                }

                StatementKind::Incr(lval, _) |
                StatementKind::Decr(lval, _) => {
                    let var = lval_to_lang_var(lval);
                    self.register_variable(var, UseType::Write);
                }

                StatementKind::Say(e) => self.observe_expr(e),
                StatementKind::Continue => {}
                StatementKind::Break => {}
                StatementKind::Return(e) => self.observe_expr(e),

                StatementKind::FuncDef(var, args, block) => {
                    self.register_variable(var.to_lang_variable(), UseType::Write);

                    self.enter_scope(statement.pos.0);

                    for arg in args.iter() {
                        self.register_variable(arg.to_lang_variable(),
                                               UseType::ForcedLocalWrite);
                    }

                    self.walk_tree(block);
                    self.exit_scope();
                }

                StatementKind::While(e, block) | StatementKind::Until(e, block) => {
                    self.observe_expr(e);
                    self.walk_tree(block);
                }

                StatementKind::Condition(e, if_block, else_block) => {
                    self.observe_expr(e);
                    self.walk_tree(if_block);
                    self.walk_tree(else_block);
                }
            }
        }
    }

    fn observe_expr(&mut self, expr: &'prog ast::Expr) {
        use syntax::ast::{Expr, Logical};

        match expr {
            Expr::LValue(lval) => {
                let var = lval_to_lang_var(lval);
                self.register_variable(var, UseType::Read);
            }
            Expr::Literal(_) => {},
            Expr::Compare(comp) => {
                let ast::Comparison(e1, _, e2) = comp.as_ref();
                self.observe_expr(e1);
                self.observe_expr(e2);
            }
            Expr::FuncCall(fn_name, args) => {
                self.observe_expr(fn_name);
                for a in args {
                    self.observe_expr(a);
                }
            }

            Expr::Add(e1, e2) |
            Expr::Sub(e1, e2) |
            Expr::Mul(e1, e2) |
            Expr::Div(e1, e2) => {
                self.observe_expr(e1);
                self.observe_expr(e2);
            }

            Expr::Logical(logical) => {
                match logical.as_ref() {
                    Logical::Not(e) => {
                        self.observe_expr(e);
                    }
                    Logical::And(e1, e2) |
                    Logical::Or(e1, e2) |
                    Logical::Nor(e1, e2) => {
                        self.observe_expr(e1);
                        self.observe_expr(e2);
                    }
                }
            }
        }
    }

    fn register_variable(&mut self, var: LangVariable<'prog>, use_type: UseType) {
        self.var_uses.entry(var)
            .or_insert_with(HashMap::new)
            .entry(self.current_scope)
                .and_modify(|u| u.merge(use_type))
                .or_insert(use_type);
    }

    fn enter_scope(&mut self, pos: SrcPos) {
        let new_scope = self.scope_parents.len() as ScopeId;
        self.scope_parents.push(Some(self.current_scope));
        self.scope_stack.push(new_scope);
        self.current_scope = new_scope;

        match self.block_scopes.entry(pos) {
            Entry::Occupied(_) => {
                panic!("Duplicate block position {}", pos);
            }
            Entry::Vacant(e) => {
                e.insert(self.current_scope);
            }
        }
    }

    fn exit_scope(&mut self) {
        self.scope_stack.pop().expect("ScopeBuilder::exit_scope");
        self.current_scope = self.scope_stack.last().cloned().unwrap_or(0);
    }
}

fn lval_to_lang_var(lval: &ast::LValue) -> LangVariable {
    match lval {
        LValue::Variable(v) => v.to_lang_variable(),
        LValue::Pronoun(..) => unimplemented!("{:?}", lval),
    }
}

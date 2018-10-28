use std::collections::BTreeMap;
use std::collections::hash_map::{HashMap, Entry};

use void::Void;

use ast::{self, Statement, StatementKind, LValue};
use ast_walker::{visit_statements, StatementVisitor, BlockType};
use lang_constructs::LangVariable;

/// A collector does a pass over the AST and notes all the variables
/// assigned and read to in different scopes.
pub fn identify_variable_scopes(program: &[Statement]) -> ScopeMap {
    let mut assign_obs = AssignmentObserver::new();
    visit_statements(program, &mut assign_obs)
        .expect("infallible traversal");

    let mut scope_map = assign_obs.to_scope_map();

    {
        let mut read_obs = UseObserver::new(&mut scope_map);
        visit_statements(program, &mut read_obs)
            .expect("infallible traversal");
    }

    scope_map
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum VariableType {
    Local,
    Global,
    Closure,
}

#[derive(Debug, Copy, Clone)]
enum UseType {
    Read,
    Write,
}

#[derive(Default, Debug, Copy, Clone)]
struct UseData {
    nonlocal_use: Option<UseType>,
}

pub struct ScopeData<'prog> {
    scope_id: ScopeId,
    // Use a binary tree to get a stable iteration order. Ideally we'd
    // probably use insertion order, but that would also push extra
    // requirements into the the scope analysis pass.
    owned_variables: BTreeMap<LangVariable<'prog>, UseData>,
    parent: Option<ScopeId>,
}

impl<'prog> ScopeData<'prog> {
    pub fn get_variable_type(&self, var: &LangVariable) -> Option<VariableType> {
        self.owned_variables.get(var).map(|use_data| {
            match use_data.nonlocal_use {
                None => VariableType::Local,
                Some(_) => {
                    if self.scope_id == 0 {
                        VariableType::Global
                    } else {
                        VariableType::Closure
                    }
                }
            }
        })
    }
}

#[derive(Default)]
pub struct ScopeMap<'prog> {
    block_scopes: HashMap<SrcPos, ScopeId>,
    scope_data: HashMap<ScopeId, ScopeData<'prog>>
}

impl<'prog> ScopeMap<'prog> {
    pub fn get_scope_for_func_declaration(&self, statement: &Statement) -> ScopeId {
        *self.block_scopes.get(&statement.pos.0)
            .unwrap_or_else(|| panic!("No scope for statement {:?}", statement))
    }

    pub fn get_owning_scope_for_var(&self,
                                    var: &LangVariable,
                                    referencing_scope: ScopeId) -> Option<ScopeId> {
        self.get_scope_data_for_owner(var, referencing_scope)
            .map(|d| d.scope_id)
    }

    pub fn get_scope_data_for_owner(&self,
                                    var: &LangVariable,
                                    referencing_scope: ScopeId) -> Option<&ScopeData>
    {
        let mut next_candidate = Some(referencing_scope);

        while let Some(current_scope) = next_candidate {
            let scope_data = self.scope_data.get(&current_scope).expect("scope lookup");
            if scope_data.owned_variables.contains_key(var) {
                return Some(scope_data);
            }
            next_candidate = scope_data.parent;
        }

        None
    }

    pub fn get_scope_data(&self, scope_id: ScopeId) -> &ScopeData {
        self.scope_data.get(&scope_id)
            .expect("get_scope_data")
    }

    pub fn get_owned_vars_for_scope(&self, scope_id: ScopeId) -> Vec<&LangVariable<'prog>> {
        if let Some(d) = self.scope_data.get(&scope_id) {
            d.owned_variables.keys().collect()
        } else {
            Vec::new()
        }
    }
}

pub type ScopeId = u64;
pub type SrcPos = usize;

struct AssignmentData {
    is_shadow_capable: bool,
}

struct AssignmentObserver<'prog> {
    scope_id_alloc: ScopeId,
    scope_stack: Vec<ScopeId>,
    block_scopes: HashMap<SrcPos, ScopeId>,
    scope_parent: HashMap<ScopeId, ScopeId>,
    assignments: HashMap<ScopeId, HashMap<LangVariable<'prog>, AssignmentData>>,
}

impl<'prog> AssignmentObserver<'prog> {
    fn new() -> Self {
        AssignmentObserver {
            scope_id_alloc: 0,
            scope_stack: vec![0],
            block_scopes: HashMap::new(),
            scope_parent: HashMap::new(),
            assignments: HashMap::new(),
        }
    }

    fn to_scope_map(self) -> ScopeMap<'prog> {
        let mut scope_data: HashMap<_, _> = self.scope_parent.into_iter()
            .map(|(scope_id, parent)| (scope_id, ScopeData {
                scope_id,
                owned_variables: BTreeMap::new(),
                parent: Some(parent),
            }))
            .collect();

        // Add the root scope
        scope_data.insert(0, ScopeData {
            scope_id: 0,
            owned_variables: BTreeMap::new(),
            parent: None,
        });

        for (scope, assignments) in &self.assignments {
            for var in assignments.keys() {
                let mut ancestor = Some(*scope);
                let mut candidate_owner = *scope;

                while let Some(s) = ancestor {
                    if let Some(data) = self.assignments.get(&s).and_then(|a| a.get(var)) {
                        candidate_owner = s;
                        if data.is_shadow_capable {
                            break;
                        }
                    }
                    ancestor = scope_data.get(&s).and_then(|data| data.parent);
                }

                // FIXME: Cloning var could be expensive and shouldn't be necessary
                scope_data.get_mut(&candidate_owner)
                    .expect("deref scope")
                    .owned_variables
                    .insert(var.clone(), UseData::default());
            }
        }

        ScopeMap {
            block_scopes: self.block_scopes,
            scope_data,
        }
    }

    fn scope(&self) -> ScopeId {
        *self.scope_stack.last().expect("AssignmentObserver scope")
    }

    fn register_lval(&mut self, lval: &'prog LValue, is_shadow_capable: bool) {
        let var;
        match lval {
            LValue::Variable(v) => var = v.to_lang_variable(),
            LValue::Pronoun(..) => unimplemented!("{:?}", lval),
        }
        self.register_variable(var, is_shadow_capable);
    }

    fn register_variable(&mut self, var: LangVariable<'prog>, is_shadow_capable: bool) {
        let scope = self.scope();
        self.assignments.entry(scope)
            .or_insert(HashMap::new())
            .entry(var)
            .and_modify(|d| {
                d.is_shadow_capable = d.is_shadow_capable || is_shadow_capable;
            })
            .or_insert(AssignmentData { is_shadow_capable });
    }
}

impl<'prog> StatementVisitor<'prog> for AssignmentObserver<'prog> {
    type Error = Void;

    fn visit_statement(&mut self, statement: &'prog Statement)
        -> Result<(), Self::Error>
    {
        match &statement.kind {
            StatementKind::Assign(lval, _) => self.register_lval(lval, false),
            _ => {}
        }
        Ok(())
    }

    fn enter_block(&mut self, block_type: BlockType, statement: &'prog Statement)
        -> Result<(), Self::Error>
    {
        if block_type != BlockType::FuncBodyBlock {
            return Ok(());
        }

        let var;
        let args;

        if let StatementKind::FuncDef(v, a, _) = &statement.kind {
            var = v;
            args = a;
        } else {
            unreachable!("{:?}", statement);
        }

        // First, assign the function name
        // FIXME: Shouldn't this be an LValue in the AST?
        self.register_variable(var.to_lang_variable(), false);

        // Push the new scope
        let current_scope = self.scope();

        self.scope_id_alloc += 1;
        let scope_id = self.scope_id_alloc;

        match self.block_scopes.entry(statement.pos.0) {
            Entry::Occupied(e) => {
                panic!("Duplicate block position: {:?} conflicts with {:?}",
                       e.get(), statement);
            }
            Entry::Vacant(e) => {
                e.insert(scope_id);
            }
        }

        self.scope_parent.insert(scope_id, current_scope);
        self.scope_stack.push(scope_id);

        // Assign the function arguments
        for arg in args {
            self.register_variable(arg.to_lang_variable(), true);
        }

        Ok(())
    }

    fn exit_block(&mut self, block_type: BlockType, _: &'prog Statement)
        -> Result<(), Self::Error>
    {
        if block_type != BlockType::FuncBodyBlock {
            return Ok(());
        }

        self.scope_stack.pop().expect("Exit func body");
        Ok(())
    }
}

struct UseObserver<'a, 'prog: 'a> {
    scope_map: &'a mut ScopeMap<'prog>,
    scope_stack: Vec<ScopeId>,
}

impl<'a, 'prog: 'a> UseObserver<'a, 'prog> {
    fn new(scope_map: &'a mut ScopeMap<'prog>) -> Self {
        UseObserver {
            scope_map,
            scope_stack: vec![0],
        }
    }

    fn observe_expr(&mut self, expr: &'prog ast::Expr) {
        use ast::{Expr, Logical};

        match expr {
            Expr::LValue(lval) => self.observe_lval(lval, UseType::Read),
            Expr::Literal(_) => {},
            Expr::Compare(comp) => {
                let ast::Comparison(e1, _, e2) = comp.as_ref();
                self.observe_expr(e1);
                self.observe_expr(e2);
            },
            Expr::FuncCall(fn_name, args) => {
                self.observe_expr(fn_name);
                for a in args {
                    self.observe_expr(a);
                }
            },

            Expr::Add(e1, e2) |
            Expr::Sub(e1, e2) |
            Expr::Mul(e1, e2) |
            Expr::Div(e1, e2) => {
                self.observe_expr(e1);
                self.observe_expr(e2);
            }

            Expr::Logical(logical) => {
                match logical.as_ref() {
                    Logical::And(e1, e2) | Logical::Or(e1, e2) => {
                        self.observe_expr(e1);
                        self.observe_expr(e2);
                    }
                }
            }
        }
    }

    fn observe_lval(&mut self, lval: &'prog ast::LValue, use_type: UseType) {
        match lval {
            ast::LValue::Variable(var) => self.observe_var(var, use_type),
            ast::LValue::Pronoun(_) => unimplemented!(),
        }
    }

    fn observe_var(&mut self, var: &'prog ast::Variable, use_type: UseType) {
        let scope = *self.scope_stack.last().expect("Scope in UseObserver");
        let lang_var = &var.to_lang_variable();

        match self.scope_map.get_owning_scope_for_var(lang_var, scope) {
            Some(owner) if owner == scope => {}
            Some(owner) => {
                let mut use_data = self.scope_map.scope_data.get_mut(&owner)
                    .expect("Deref owning scope")
                    .owned_variables
                    .get_mut(lang_var)
                    .expect("Deref var in owning scope");

                let new_use_type = match use_data.nonlocal_use {
                    None | Some(UseType::Read) => use_type,
                    Some(UseType::Write) => UseType::Write,
                };

                use_data.nonlocal_use = Some(new_use_type);
            }
            None => unreachable!(),
        }
    }
}

impl<'a, 'prog: 'a> StatementVisitor<'prog> for UseObserver<'a, 'prog> {
    type Error = Void;

    fn visit_statement(&mut self, statement: &'prog Statement)
        -> Result<(), Self::Error>
    {
        match &statement.kind {
            StatementKind::Assign(lval, e) => {
                self.observe_lval(lval, UseType::Write);
                self.observe_expr(e);
            }
            StatementKind::Incr(lval) |
            StatementKind::Decr(lval) => {
                self.observe_lval(lval, UseType::Write);
            }
            StatementKind::Say(e) => self.observe_expr(e),

            StatementKind::Continue => {}
            StatementKind::Break => {}
            StatementKind::Return(e) => self.observe_expr(e),

            StatementKind::Condition(cond, _, _) |
            StatementKind::While(cond, _) |
            StatementKind::Until(cond, _) => self.observe_expr(cond),

            StatementKind::FuncDef(fname, _, _) => {
                self.observe_var(fname, UseType::Write);
            }
        }
        Ok(())
    }

    fn enter_block(&mut self, block_type: BlockType, statement: &'prog Statement)
        -> Result<(), Self::Error>
    {
        if block_type != BlockType::FuncBodyBlock {
            return Ok(());
        }

        let new_scope = self.scope_map.get_scope_for_func_declaration(statement);
        self.scope_stack.push(new_scope);

        Ok(())
    }

    fn exit_block(&mut self, block_type: BlockType, _: &'prog Statement)
        -> Result<(), Self::Error>
    {
        if block_type != BlockType::FuncBodyBlock {
            return Ok(());
        }

        self.scope_stack.pop().expect("Exit func body");
        Ok(())
    }
}

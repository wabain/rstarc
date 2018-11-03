use std::collections::BTreeMap;
use std::collections::hash_map::{HashMap, Entry};
use std::mem::replace;

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
}

#[derive(Debug, Clone)]
enum ClosureSource {
    Local { idx: usize },
    Parent { closure_idx: usize, idx: usize },
}

/// Storage type for a variable
#[derive(Debug, Clone)]
enum StorageType {
    Global,
    Local { scope_id: ScopeId, idx: usize },
    Closure { scope_id: ScopeId, src: ClosureSource },
}

impl<'a> Into<VariableType> for &'a StorageType {
    fn into(self) -> VariableType {
        match *self {
            StorageType::Global => VariableType::Global,
            StorageType::Local { scope_id, .. } => VariableType::Local(scope_id),
            StorageType::Closure { scope_id, .. } => VariableType::Closure(scope_id),
        }
    }
}

/// Data associated with a given scope. Each ScopeData instance contains ***.
#[derive(Default, Debug, Clone)]
struct ScopeData<'prog> {
    // Use a binary tree to get a stable iteration order. Ideally we'd
    // probably use insertion order, but that would also push extra
    // requirements into the the scope analysis pass.
    used_variables: BTreeMap<LangVariable<'prog>, StorageType>,
    /// Count of closure variables initiated in this scope
    local_scope_closure_var_count: usize,
    /// Count of local variables used in this scope
    local_var_count: usize,
}

impl<'prog> ScopeData<'prog> {
    fn get_storage_type<'a>(&'a self, var: &'a LangVariable) -> Option<&'a StorageType> {
        self.used_variables.get(var)
    }
}

#[derive(Default)]
pub struct ScopeMap<'prog> {
    block_scopes: HashMap<SrcPos, ScopeId>,
    scope_data: Vec<ScopeData<'prog>>
}

impl<'prog> ScopeMap<'prog> {
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
            .map(Into::into)
    }

    pub fn get_owned_vars_for_scope(&self, scope_id: ScopeId)
        -> impl Iterator<Item=(&LangVariable<'prog>, VariableType)>
    {
        self.scope_data(scope_id)
            .used_variables.iter()
            .filter(move |(_, t)| {
                let vt: VariableType = (*t).into();
                vt.owner() == scope_id
            })
            .map(|(k, t)| (k, {
                let vt: VariableType = t.into();
                vt
            }))
    }

    fn scope_data(&self, scope_id: ScopeId) -> &ScopeData<'prog> {
        self.scope_data.get(scope_id as usize).unwrap_or_else(|| {
            panic!("Missing scope data for scope {}", scope_id)
        })
    }
}

type FuncParams<'a> = (SrcPos, &'a [ast::Variable], &'a [Statement]);

#[derive(Debug, PartialEq, Clone, Copy)]
enum StorageTypeSpec {
    LocalScope { has_nonlocal_access: bool },
    ParentScope { owner: ScopeId },
}

impl StorageTypeSpec {
    fn local() -> Self {
        StorageTypeSpec::LocalScope { has_nonlocal_access: false }
    }

    fn merge(&mut self, other: &StorageTypeSpec) {
        use self::StorageTypeSpec::*;
        match (self, other) {
            (LocalScope { has_nonlocal_access: a },
             LocalScope { has_nonlocal_access: b }) => {
                if *b && !*a {
                    *a = true;
                }
            }

            (ParentScope { owner: a },
             ParentScope { owner: b }) if a == b => {},

            (s, o) => panic!("Incompatible XXX types: {:?} and {:?}", s, o),
        };
    }
}

#[derive(Default, Debug)]
struct ScopeBuildingParams<'prog> {
    inorder_vars: Vec<StorageTypeSpec>,
    var_map: HashMap<LangVariable<'prog>, usize>,
}

impl<'prog> ScopeBuildingParams<'prog> {
    fn to_scope_data(self, prev: &[ScopeData]) -> ScopeData<'prog> {
        let scope_id = prev.len() as ScopeId;

        let mut parent_closure_idxs = HashMap::new();
        let mut local_scope_closure_var_count = 0;
        let mut local_var_count = 0;

        let mut inorder_used_vars: Vec<_>;

        {
            let mut inorder_var_src: Vec<_> = self.var_map.iter().collect();
            inorder_var_src.sort_by_key(|(_, &idx)| idx);

            inorder_used_vars = self.inorder_vars.into_iter()
                .enumerate()
                .map(|(var_idx, spec)| {
                    let t = match spec {
                        StorageTypeSpec::LocalScope { has_nonlocal_access: false } => {
                            let idx = local_var_count;
                            local_var_count += 1;
                            StorageType::Local { scope_id, idx }
                        }
                        StorageTypeSpec::LocalScope { has_nonlocal_access: true } => {
                            if scope_id == 0 {
                                return Some(StorageType::Global);
                            }

                            let idx = local_scope_closure_var_count;
                            local_scope_closure_var_count += 1;
                            StorageType::Closure {
                                scope_id,
                                src: ClosureSource::Local { idx },
                            }
                        }
                        StorageTypeSpec::ParentScope { owner } => {
                            let var = inorder_var_src[var_idx].0;

                            let parent_type = prev[owner as usize]
                                .get_storage_type(var)
                                .expect("owner storage type");

                            match *parent_type {
                                StorageType::Global => StorageType::Global,

                                StorageType::Closure {
                                    src: ClosureSource::Local { idx },
                                    ..
                                } => {
                                    let parent_closure_idxs_count = parent_closure_idxs.len();
                                    let closure_idx = *parent_closure_idxs.entry(owner)
                                        .or_insert(parent_closure_idxs_count);

                                    StorageType::Closure {
                                        scope_id: owner,
                                        src: ClosureSource::Parent { closure_idx, idx },
                                    }
                                }

                                _ => unreachable!("parent storage type {:?}", parent_type),
                            }
                        }
                    };
                    Some(t)
                })
                .collect();
        }

        let used_vars = self.var_map.into_iter()
            .map(|(var, idx)| {
                (var, inorder_used_vars[idx].take().expect("Take inorder"))
            })
            .collect();

        ScopeData {
            used_variables: used_vars,
            local_scope_closure_var_count,
            local_var_count,
        }
    }

    fn add_var(&mut self,
               var: LangVariable<'prog>,
               var_type: StorageTypeSpec)
    {
        match self.var_map.entry(var) {
            Entry::Occupied(e) => {
                let prior_type = &mut self.inorder_vars[*e.get()];
                prior_type.merge(&var_type);
            }
            Entry::Vacant(e) => {
                let idx = self.inorder_vars.len();
                self.inorder_vars.push(var_type);
                e.insert(idx);
            }
        }
    }

    fn set_nonlocal_access(&mut self, var: &LangVariable) {
        let idx = *self.var_map.get(var).unwrap_or_else(|| {
            panic!("set_nonlocal_access for missing var {:?}", var)
        });
        match self.inorder_vars[idx] {
            StorageTypeSpec::LocalScope { has_nonlocal_access: ref mut a } => {
                *a = true;
            }
            ref t @ _ => {
                panic!("set_nonlocal_access for {:?} with type {:?}", var, t);
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

/// *** to build the scope map. The procedure is as follows:
///
/// 1. Walk through each scope of the AST to track which scope owns each
///    variable.
///
/// 2. Determine storage type for each variable based on whether it is used
///    in another scope.
#[derive(Default)]
struct ScopeMapBuilder<'prog> {
    current_scope: ScopeId,
    scope_stack: Vec<ScopeId>,
    scope_parents: Vec<Option<ScopeId>>,
    scope_params: Vec<ScopeBuildingParams<'prog>>,
    scope_data: HashMap<ScopeId, ScopeData<'prog>>,
    var_owners: HashMap<(LangVariable<'prog>, ScopeId), ScopeId>,
    block_scopes: HashMap<SrcPos, ScopeId>,
    child_functions: Vec<FuncParams<'prog>>,
}

impl<'prog> ScopeMapBuilder<'prog> {
    fn new() -> Self {
        let mut scope_data = HashMap::new();
        scope_data.insert(0, ScopeData::default());

        ScopeMapBuilder {
            scope_parents: vec![None],
            scope_stack: vec![0],
            scope_params: vec![ScopeBuildingParams::default()],
            scope_data,
            ..Self::default()
        }
    }

    fn to_scope_map(mut self) -> ScopeMap<'prog> {
        // Exit the root scope
        self.exit_root_scope();
        assert!(self.scope_stack.is_empty());

        let scope_data = self.scope_params.into_iter()
            .fold(Vec::new(), |mut prev, params| {
                let new = params.to_scope_data(&prev);
                prev.push(new);
                prev
            });

        // eprintln!("{:?}", scope_data);

        ScopeMap {
            block_scopes: self.block_scopes,
            scope_data,
        }
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
                    self.child_functions.push((statement.pos.0, args, block));
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
        let current_scope = self.current_scope;

        // Forced local: shadow any assignments in ancestor scopes
        if use_type == UseType::ForcedLocalWrite {
            let var_type = StorageTypeSpec::local();
            self.add_var(current_scope, current_scope, var, var_type);
            return;
        }

        // Search the scope tree for someone who owns the variable
        let mut scope_id = Some(current_scope);

        while let Some(reg_id) = scope_id {
            // Search for a scope which has registered the variable
            let owner = match self.var_owners.get(&(var.clone(), reg_id)) {
                Some(&owner) => owner,
                None => {
                    scope_id = self.scope_parents[reg_id as usize];
                    continue;
                }
            };

            // Add the variable
            let var_type;

            if owner == current_scope {
                var_type = StorageTypeSpec::local();
            } else {
                var_type = StorageTypeSpec::ParentScope { owner };
                self.scope_params[owner as usize].set_nonlocal_access(&var);
            }

            self.add_var(current_scope, owner, var.clone(), var_type);

            // Each scope between the previously registering scope and the
            // current scope needs to register the variable
            let mut stack_idx = self.scope_stack.len();
            while stack_idx > 0 {
                stack_idx -= 1;
                let ancestor = self.scope_stack[stack_idx];
                if ancestor == reg_id {
                    return;
                }
                self.add_var(ancestor, owner, var.clone(), var_type);
            }

            unreachable!("owner scope was not ancestor of current scope");
        }

        // Fallthrough: no ancestor scope has registered the variable
        let var_type = StorageTypeSpec::local();
        self.add_var(current_scope, current_scope, var, var_type);
    }

    fn add_var(&mut self,
               scope_id: ScopeId,
               owner_id: ScopeId,
               var: LangVariable<'prog>,
               var_type: StorageTypeSpec)
    {
        self.scope_params[scope_id as usize].add_var(var.clone(), var_type);
        self.var_owners.insert((var, scope_id), owner_id);
    }

    fn enter_scope(&mut self, pos: SrcPos) {
        assert!(self.child_functions.is_empty());

        let new_scope = self.scope_parents.len() as ScopeId;
        self.scope_parents.push(Some(self.current_scope));
        self.scope_params.push(ScopeBuildingParams::default());
        self.scope_stack.push(new_scope);
        self.scope_data.insert(new_scope, ScopeData::default());

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

    fn exit_root_scope(&mut self) {
        self.exit_scope_internal();
    }

    fn exit_scope(&mut self) {
        self.exit_scope_internal();
        self.current_scope = self.scope_stack.last().cloned().expect("ScopeBuilder::exit_scope::scope_stack.last()");  // XXX
    }

    fn exit_scope_internal(&mut self) {
        let child_functions = replace(&mut self.child_functions, Vec::new());

        for (pos, args, block) in child_functions {
            self.enter_scope(pos);

            for arg in args.iter() {
                self.register_variable(arg.to_lang_variable(),
                                       UseType::ForcedLocalWrite);
            }

            self.walk_tree(block);
            self.exit_scope();
        }

        self.scope_stack.pop().expect("ScopeBuilder::exit_scope::pop");
    }
}

fn lval_to_lang_var(lval: &ast::LValue) -> LangVariable {
    match lval {
        LValue::Variable(v) => v.to_lang_variable(),
        LValue::Pronoun(..) => unimplemented!("{:?}", lval),
    }
}

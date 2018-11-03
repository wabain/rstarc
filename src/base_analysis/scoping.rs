use std::hash::Hash;
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

/// Each entry in a closure can either be a variable or a pointer to an
/// ancestor scope's closure
#[derive(Debug, Clone)]
enum ClosureEntry<'prog> {
    Variable(LangVariable<'prog>),
    Closure(ScopeId),
}

/// Data associated with a given scope. Each ScopeData instance contains ***.
#[derive(Default, Debug, Clone)]
struct ScopeData<'prog> {
    // Use a binary tree to get a stable iteration order. Ideally we'd
    // probably use insertion order, but that would also push extra
    // requirements into the the scope analysis pass.
    used_variables: BTreeMap<LangVariable<'prog>, VariableType>,
    /// Scopes from which this scope takes a closure. Each closure can be
    /// local to the current scope, or reexported as part of this scope's
    /// closure.
    used_closures: HashMap<ScopeId, VariableType>,
    /// A list of the entries owned by this closure
    closure_layout: Vec<ClosureEntry<'prog>>,
}

impl<'prog> ScopeData<'prog> {
    fn access_nonlocal(&mut self, var: &LangVariable<'prog>) -> VariableType {
        let var_type = self.used_variables.get_mut(var)
            .expect("access_nonlocal lookup");

        match *var_type {
            VariableType::Local(s) => {
                let closure_idx = self.closure_layout.len();
                self.closure_layout.push(ClosureEntry::Variable(var.clone()));
                *var_type = VariableType::Closure(s);
                return *var_type
            }
            VariableType::Closure(_) | VariableType::Global => return *var_type
        }
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
            .cloned()
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

type FuncParams<'a> = (SrcPos, &'a [ast::Variable], &'a [Statement]);

#[derive(Debug, PartialEq, Clone, Copy)]
enum ScopeBuildingVarType {
    Local { has_nonlocal_access: bool },
    NonLocal { owner: ScopeId },
}

impl ScopeBuildingVarType {
    fn could_become(&self, other: &ScopeBuildingVarType) -> bool {
        use self::ScopeBuildingVarType::*;
        match (self, other) {
            (Local { has_nonlocal_access: true },
             Local { has_nonlocal_access: true }) |
            (Local { has_nonlocal_access: false },
             Local { has_nonlocal_access: _ }) => true,

            (NonLocal { owner: a },
             NonLocal { owner: b }) if a == b => true,

            _ => false,
        }
    }
}

#[derive(Default, Debug)]
struct ScopeBuildingParams<'prog> {
    inorder_vars: Vec<ScopeBuildingVarType>,
    var_map: HashMap<LangVariable<'prog>, usize>,
}

impl<'prog> ScopeBuildingParams<'prog> {
    fn to_scope_data(self, prev: &[ScopeData]) -> ScopeData<'prog> {
        // let mut closure_vars

        let scope_id = prev.len() as ScopeId;

        let mut inorder_used_vars: Vec<_> = self.inorder_vars.into_iter()
            .map(|build_t| {
                let scope_id = scope_id as u64;
                let t = match build_t {
                    ScopeBuildingVarType::Local { has_nonlocal_access: false } => {
                        VariableType::Local(scope_id)
                    }
                    ScopeBuildingVarType::Local { has_nonlocal_access: true } => {
                        if scope_id == 0 {
                            VariableType::Global
                        } else {
                            VariableType::Closure(scope_id)
                        }
                    }
                    ScopeBuildingVarType::NonLocal { owner } => {
                        VariableType::Closure(owner)
                    }
                };
                Some(t)
            })
            .collect();

        let used_vars = self.var_map.into_iter()
            .map(|(var, idx)| {
                (var, inorder_used_vars[idx].take().expect("Take inorder"))
            })
            .collect();

        ScopeData {
            used_variables: used_vars,
            ..ScopeData::default()
        }
    }

    fn has(&self, var: &LangVariable) -> bool {
        self.var_map.contains_key(var)
    }

    fn add_var(&mut self,
               var: LangVariable<'prog>,
               building_var_type: ScopeBuildingVarType)
    {
        match self.var_map.entry(var) {
            Entry::Occupied(e) => {
                // XXX: Should do merge?
                let prior_type = &self.inorder_vars[*e.get()];
                debug_assert!(building_var_type.could_become(prior_type));
            }
            Entry::Vacant(e) => {
                let idx = self.inorder_vars.len();
                self.inorder_vars.push(building_var_type);
                e.insert(idx);
            }
        }
    }

    fn set_nonlocal_access(&mut self, var: &LangVariable) {
        let idx = *self.var_map.get(var).unwrap_or_else(|| {
            panic!("set_nonlocal_access for missing var {:?}", var)
        });
        match self.inorder_vars[idx] {
            ScopeBuildingVarType::Local { has_nonlocal_access: ref mut a } => {
                *a = true;
            }
            ref t @ _ => {
                panic!("set_nonlocal_access for {:?} with type {:?}", var, t);
            }
        }
    }
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

        // let scope_data = (0..self.scope_parents.len()).into_iter()
        //     .map(|i| self.scope_data.remove(&(i as ScopeId))
        //         .unwrap_or_else(|| panic!("Missing scope data for scope {}", i)))
        //     .collect();

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
            let var_type = ScopeBuildingVarType::Local { has_nonlocal_access: false };
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
                var_type = ScopeBuildingVarType::Local { has_nonlocal_access: false };
            } else {
                var_type = ScopeBuildingVarType::NonLocal { owner };
                self.scope_params[owner as usize].set_nonlocal_access(&var);
            }

            self.add_var(current_scope, owner, var.clone(), var_type);

            // Each scope between the previously registering scope and the
            // current scope needs to register the variable
            let mut chain_idx = self.scope_stack.len();
            while chain_idx > 0 {
                chain_idx -= 1;
                let ancestor = self.scope_stack[chain_idx];
                if ancestor == reg_id {
                    return;
                }
                self.add_var(ancestor, owner, var.clone(), var_type);
            }

            unreachable!("owner scope was not ancestor of current scope");
        }

        // Fallthrough: no ancestor scope has registered the variable
        let var_type = ScopeBuildingVarType::Local { has_nonlocal_access: false };
        self.add_var(current_scope, current_scope, var, var_type);
    }

    fn add_var(&mut self,
               scope_id: ScopeId,
               owner_id: ScopeId,
               var: LangVariable<'prog>,
               var_type: ScopeBuildingVarType)
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

fn into_sorted_by_key<K, V>(map: HashMap<K, V>) -> Vec<(K, V)>
    where K: Eq + Hash + Ord + Clone
{
    let mut var_uses: Vec<_> = map.into_iter().collect();
    var_uses.sort_by_key(|(k, _)| k.clone());
    var_uses
}

fn lval_to_lang_var(lval: &ast::LValue) -> LangVariable {
    match lval {
        LValue::Variable(v) => v.to_lang_variable(),
        LValue::Pronoun(..) => unimplemented!("{:?}", lval),
    }
}

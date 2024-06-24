//! Interface and structures of the symbol table for our C1 interpreter.
//!
//! # Overview
//!
//! This file defines the data structures and functions for managing a
//! symbol table, which is useful for semantic analysis in the parser. The symbol
//! table stores information about identifiers, their data types, and nests their
//! scopes.
//!
//! The main structures include:
//! - [`FuncInfo`]: Represents a function, including return type and local variables.
//! - [`VarInfo`]: Represents a variable, including its data type and index in the
//!   definition table.
//! - [`DefInfo`]: Parent structure for a definition, which can encompass both
//!   functions and variables.
//! - [`Symtab`]: The main structure of the symbol table, managing identifiers and
//!   their definitions.
//!
//! The provided functions enable the creation and release of symbol tables, the
//! definition of functions and variables, the entering and leaving of scopes,
//! and the searching and resolving of identifiers.
//!
//! # Auxiliary information
//!
//! The auxiliary information of all definitions is stored a single vector in
//! [`Definitions`]. The [`ast::DefId`] that is stored directly in the AST as part of
//! the [`ast::ResIdent`]s represents an index into this vector of definitions.
//!
//! The [`FuncInfo`] and [`VarInfo`] contain the auxiliary information required
//! by the interpreter about function and variable definitions respectively. When stored
//! in the [`Definitions`], they are combined in the enum [`DefInfo`].
//!
//! The top-level auxiliary data structure produced by the [`analyze`] function is
//! [`ProgramInfo`], which contains the [`Definitions`] and some additional
//! information about the main function and global variables.

use std::{
    collections::{hash_map::Entry, HashMap},
    ops::Index,
};

use crate::ast;

/// Block-structured symbol table.
#[derive(Debug, Clone, PartialEq)]
pub struct Symtab {
    /// The block-structure of the symbol table.
    ///
    /// * `scopes[0]` is always the global scope.
    /// * `scopes[1]` is always the function scope (if present).
    /// * More scopes are blocks inside functions (if present).
    scopes: Vec<HashMap<ast::Ident, ast::DefId>>,
    /// The map from [`ast::DefId`] to [`DefInfo`].
    definitions: Definitions,
    /// The function definition that is currently being analyzed.
    current_func: Option<FuncDefId>,
    /// A list of all global variables.
    global_vars: Vec<ast::GlobalVarItemId>,
}

impl Symtab {
    /// Extracts the relevant fields from the [`Symtab`] and constructs the
    /// top-level info-object from them.
    ///
    /// This method strips all of the superfluous information that is not
    /// required by the interpreter.
    pub fn into_program_info(self) -> super::ProgramInfo {
        super::ProgramInfo {
            definitions: self.definitions,
            global_vars: self.global_vars,
            main_func: None,
        }
    }

    /// Creates a new scope in the block-structured symbol table.
    ///
    /// The new scope will be used for new definitions.
    pub fn scope_enter(&mut self) {
        self.scopes.push(HashMap::new());
    }

    /// Pops the innermost scope of the block-structured symbol table.
    ///
    /// This makes all symbols from the innermost scope inaccessible.
    pub fn scope_leave(&mut self) {
        assert!(!self.scopes.is_empty());
        self.scopes.pop();

        if self.is_global_scope() {
            self.current_func = None;
        }
    }

    /// Returns a mutable reference to the function that's currently being
    /// analyzed or `None` in the global scope.
    pub fn current_func(&mut self) -> Option<&mut FuncInfo> {
        self.current_func
            .map(|func| self.definitions.get_func_mut(func))
    }

    /// Resolves a resolvable identifier to a definition.
    ///
    /// # Panics
    ///
    /// Panic if called multiple times on the same [`ast::ResIdent`].
    pub fn resolve(&self, ident: &str) -> Result<ast::DefId, ResolveError> {
        for scope in self.scopes.iter().rev() {
            if let Some(&def_id) = scope.get(ident) {
                return Ok(def_id);
            }
        }
        Err(ResolveError(ident.to_owned()))
    }

    /// Returns whether the current scope is global or not.
    fn is_global_scope(&self) -> bool {
        self.scopes.len() == 1
    }

    /// Creates a new definition.
    ///
    /// This is a "low-level" operation, use the other `define_*` methods instead if able.
    fn define(&mut self, ident: ast::Ident, analysis: DefInfo) -> Result<ast::DefId, DefineError> {
        let def_id = self.definitions.push(analysis);

        let innermost_scope = self.scopes.last_mut().expect("missing root scope");
        match innermost_scope.entry(ident) {
            Entry::Vacant(entry) => {
                entry.insert(def_id);
                Ok(def_id)
            }
            Entry::Occupied(entry) => Err(DefineError(entry.key().to_string())),
        }
    }

    /// Defines a new function in the global scope.
    pub fn define_func(
        &mut self,
        ident: ast::Ident,
        return_type: ast::DataType,
        param_count: usize,
        item_id: ast::FuncItemId,
    ) -> Result<ast::DefId, DefineError> {
        assert!(
            self.is_global_scope(),
            "functions must be defined in the global scope"
        );

        // The local vars are populated by `define_local_var` later.
        let analysis = DefInfo::Func(FuncInfo {
            item_id,
            return_type,
            param_count,
            local_vars: Vec::new(),
        });

        let def_id = self.define(ident, analysis)?;
        self.current_func = Some(FuncDefId(def_id));
        Ok(def_id)
    }

    /// Defines a new global variable in the global scope.
    ///
    /// Also adds the variable to the list of global variables.
    pub fn define_global_var(
        &mut self,
        ident: &ast::Ident,
        data_type: ast::DataType,
        item_id: ast::GlobalVarItemId,
    ) -> Result<ast::DefId, DefineError> {
        assert!(
            self.is_global_scope(),
            "global variables must be defined in the global scope"
        );

        let analysis = DefInfo::GlobalVar(VarInfo {
            offset: self.global_vars.len(),
            data_type,
        });
        let def_id = self.define(ident.clone(), analysis)?;
        self.global_vars.push(item_id);
        Ok(def_id)
    }

    /// Defines a new local variable (or parameter) in the current function scope.
    ///
    /// Also adds the variable to the list of local variables of the current function.
    pub fn define_local_var(
        &mut self,
        ident: &ast::Ident,
        data_type: ast::DataType,
    ) -> Result<ast::DefId, DefineError> {
        assert!(
            !self.is_global_scope(),
            "local variables must be defined in functions"
        );

        let analysis = DefInfo::LocalVar(VarInfo {
            offset: self.current_func().unwrap().local_vars.len(),
            data_type,
        });
        let def_id = self.define(ident.clone(), analysis)?;
        self.current_func()
            .unwrap()
            .local_vars
            .push(LocalVarDefId(def_id));
        Ok(def_id)
    }
}

impl Default for Symtab {
    fn default() -> Self {
        Symtab {
            scopes: vec![HashMap::new()],
            definitions: Default::default(),
            current_func: None,
            global_vars: vec![],
        }
    }
}

impl Index<ast::DefId> for Symtab {
    type Output = DefInfo;

    fn index(&self, index: ast::DefId) -> &Self::Output {
        &self.definitions.definitions[index.0]
    }
}

impl Index<LocalVarDefId> for Symtab {
    type Output = VarInfo;

    fn index(&self, index: LocalVarDefId) -> &Self::Output {
        &self.definitions[index]
    }
}

impl Index<FuncDefId> for Symtab {
    type Output = FuncInfo;

    fn index(&self, index: FuncDefId) -> &Self::Output {
        &self.definitions[index]
    }
}

/// An error returned by [`Analyzer::define`] if the symbol is already
/// defined in the innermost scope.
pub struct DefineError(pub String);

/// An error returned by [`Analyzer::resolve`] if the symbol cannot be found.
pub struct ResolveError(pub String);

/// The information about a definition that is collected during analysis.
#[derive(Debug, Clone, PartialEq)]
pub enum DefInfo {
    Func(FuncInfo),
    GlobalVar(VarInfo),
    LocalVar(VarInfo),
}

/// The information about a function that is collected during analysis.
///
/// Includes the location of the AST node, the return type, and the count and
/// types of parameters and local variables.
#[derive(Debug, Clone, PartialEq)]
pub struct FuncInfo {
    pub item_id: ast::FuncItemId,
    pub return_type: ast::DataType,
    pub param_count: usize,
    /// Includes the parameters.
    pub local_vars: Vec<LocalVarDefId>,
}

impl FuncInfo {
    /// Returns the function parameters.
    pub fn params(&self) -> &[LocalVarDefId] {
        &self.local_vars[..self.param_count]
    }

    /// Returns the local variables that aren't parameters.
    pub fn non_param_vars(&self) -> &[LocalVarDefId] {
        &self.local_vars[self.param_count..]
    }
}

/// The information about a (local or global) variable that is collected during analysis.
///
/// Includes the storage location and the data type.
#[derive(Debug, Clone, PartialEq)]
pub struct VarInfo {
    /// For local variables: Offset in the function frame.
    ///
    /// For global variables: Offset in the global frame.
    pub offset: usize,
    pub data_type: ast::DataType,
}

/// Stores the mapping from [`ast::DefId`] to [`DefInfo`].
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Definitions {
    /// Indexed by [`ast::DefId`].
    definitions: Vec<DefInfo>,
}

impl Definitions {
    /// Creates a new definition and returns its ID.
    fn push(&mut self, analysis: DefInfo) -> ast::DefId {
        let def_id = ast::DefId(self.definitions.len());
        self.definitions.push(analysis);
        def_id
    }

    /// Returns a mutable reference to a [`FuncInfo`].
    ///
    /// This method is used to define function parameters and local variables.
    ///
    /// We don't implement [`IndexMut`], because this method should be private.
    ///
    /// [`IndexMut`]: std::ops::IndexMut
    fn get_func_mut(&mut self, id: FuncDefId) -> &mut FuncInfo {
        match &mut self.definitions[id.def_id().0] {
            DefInfo::Func(analysis) => analysis,
            analysis => unreachable!("expected {id:?} to be a function, found {analysis:?}"),
        }
    }
}

/// Identifies a function definition in [`Definitions`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FuncDefId(pub ast::DefId);

impl FuncDefId {
    #[inline]
    pub fn def_id(&self) -> ast::DefId {
        self.0
    }
}

/// Identifies a local variable (or function parameter) definition in [`Definitions`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct LocalVarDefId(pub ast::DefId);

impl LocalVarDefId {
    #[inline]
    pub fn def_id(&self) -> ast::DefId {
        self.0
    }
}

impl Index<ast::DefId> for Definitions {
    type Output = DefInfo;

    fn index(&self, id: ast::DefId) -> &Self::Output {
        &self.definitions[id.0]
    }
}

impl Index<LocalVarDefId> for Definitions {
    type Output = VarInfo;

    fn index(&self, id: LocalVarDefId) -> &Self::Output {
        match &self[id.0] {
            DefInfo::LocalVar(analysis) => analysis,
            analysis => {
                unreachable!("expected {id:?} to be a local variable, found {analysis:?}")
            }
        }
    }
}

impl Index<FuncDefId> for Definitions {
    type Output = FuncInfo;

    fn index(&self, id: FuncDefId) -> &Self::Output {
        match &self[id.0] {
            DefInfo::Func(analysis) => analysis,
            analysis => unreachable!("expected {id:?} to be a function, found {analysis:?}"),
        }
    }
}

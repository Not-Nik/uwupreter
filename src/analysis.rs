//! The semantic analysis pass of C1.
//!
//! # Overview
//!
//! The entry point of the semantic analysis pass is the [`analyze`] function.
//! It is called on the AST root ([`ast::Program`]) after parsing and has the
//! following three goals:
//!
//! - Checking the static semantic of the program, i.e. performing all "compile-time"
//!   checks. For example, this includes checking whether the operands of an addition
//!   like `a + b` are compatible. If a static semantic rule is violated, [`analyze`]
//!   returns a human-readable error message in [`AnalysisError`].
//!
//! - Collecting auxiliary information about the definition of functions and variables
//!   that will be used by the interpreter. For example, this includes the size of the
//!   stack frame for every function, i.e. how many local variables it has. If no error
//!   occurs, [`analyze`] returns this information as [`ProgramInfo`].
//!
//! - Resolving all resolvable identifiers ([`ast::ResIdent`]s) to a definition. The
//!   resolutions are written directly into the AST with [`ast::ResIdent::set_res`].
//!
//! The central data type that powers our semantic analysis pass is the [`Analyzer`],
//! which uses its `visit_*` methods to traverses the AST in a depth-first manner,
//! similar to the [visitor pattern].
//!
//! [visitor pattern]: https://en.wikipedia.org/wiki/Visitor_pattern
//!
//! # Static semantic
//!
//! The full semantic rules are provided in a separate document. The analyzer checks
//! the rules in the `visit_*` methods and bubbles out the first error that it encounters
//! via the try (`?`) operator. We do not attempt error recovery.
//!
//! # Name resolution
//!
//! The analyzer uses a block-structured symbol table ([`Symtab`]) to do name
//! resolution.
//!
//! Scopes are crated and deleted with the [`Symtab::scope_enter`] and [`Symtab::scope_leave`]
//! functions. New symbols in the innermost scope are created with the `Symtab::define_*` family
//! of methods and symbols are resolved with the [`Symtab::resolve`] method.
//!
//! Calling `resolve` returns a `DefId`, which can be used as index into [`Analyzer`]
//! to retrieve additional information about the definition.
//!
//! # Examples
//!
//! This example demonstrates how to use the public API of this module: We use the auxiliary
//! information and resolved names produced by the semantic analysis to query some information
//! about our program:
//!
//! ```
//! use uwupreter::{ast, analysis};
//!
//! let input = "void main() {
//!     int answer = 42;
//!     print(answer);
//! }";
//!
//! let mut ast = ast::parse(input).unwrap();
//! let analysis = analysis::analyze(&mut ast).unwrap();
//!
//! // How many local variables does main have?
//! let main_func_analysis = &analysis[analysis.main_func.unwrap()];
//! let main_locals = main_func_analysis.local_vars.len();
//! assert_eq!(main_locals, 1);
//!
//! // What definition did `answer` in `print(answer)` resolve to?
//! let main_func_item = &ast[main_func_analysis.item_id];
//! let ast::Stmt::Print(print_stmt) = &main_func_item.statements[1] else { unreachable!() };
//! let ast::PrintStmt::Expr(ast::Expr::Var(answer_res)) = print_stmt else { unreachable!() };
//! let answer_def_id = answer_res.get_res();
//! assert_eq!(answer_def_id, ast::DefId(1));
//!
//! // What memory location should `answer` in `print(answer)` be loaded from?
//! let answer_analysis = &analysis.definitions[answer_def_id];
//! // (The real interpreter should also handle `analysis::DefAnalysis::GlovalVar` here.)
//! let analysis::DefInfo::LocalVar(var_analysis) = answer_analysis else { unreachable!() };
//! assert_eq!(var_analysis.offset, 0);
//! ```
//!
//! Passing in an invalid program will produce an error:
//!
//! ```
//! use uwupreter::{ast, analysis};
//!
//! let input = "void main() {
//!     int x = true;
//! }";
//!
//! let mut ast = ast::parse(input).unwrap();
//! let error = analysis::analyze(&mut ast).unwrap_err();
//! println!("{error}");
//! ```

use std::fmt;
use std::ops::Index;

pub use symtab::{DefInfo, Definitions, FuncDefId, FuncInfo, LocalVarDefId, Symtab, VarInfo};

use crate::ast;
use crate::ast::{BinOp, DataType, DefId};

mod symtab;

/// The entry function of the semantic analysis pass.
pub fn analyze(root: &mut ast::Program) -> Result<ProgramInfo, AnalysisError> {
    let mut analyser = Analyzer::default();

    for (index, item) in root.items.iter_mut().enumerate() {
        let item_id = ast::ItemId(index);
        analyser.visit_item(item_id, item)?;
    }

    let resolved = analyser.tab.resolve("main");

    let Ok(def) = resolved else {
        return Err(AnalysisError(String::from("main not defined")));
    };

    let def_info = &analyser.tab[def];

    let DefInfo::Func(func_info) = def_info else {
        return Err(AnalysisError(String::from("main is not a function")));
    };

    if func_info.param_count > 0 {
        return Err(AnalysisError(String::from("main shouldn't take args")));
    }

    if func_info.return_type != DataType::Void {
        return Err(AnalysisError(String::from("main should return void")));
    }

    let mut info = analyser.tab.into_program_info();

    info.main_func = Some(FuncDefId(def));

    Ok(info)
}

/// The visitor that drives the semantic analysis pass.
#[derive(Debug, Clone, PartialEq, Default)]
pub struct Analyzer {
    /// The block-structured symbol table.
    tab: Symtab,
}

impl Analyzer {
    // Used when assigning
    fn is_compatible(lhs: DataType, rhs: DataType) -> bool {
        (lhs == rhs) || (lhs == DataType::Float && rhs == DataType::Int)
    }

    fn get_variable_type(&mut self, id: DefId) -> Result<DataType, AnalysisError> {
        let def_info = &self.tab[id];

        match def_info {
            DefInfo::Func(_) => {
                return Err(AnalysisError(String::from("can't treat function as variable")))
            }
            DefInfo::LocalVar(var) | DefInfo::GlobalVar(var) => Ok(var.data_type),
        }
    }

    /// Analyzes an item.
    fn visit_item(
        &mut self,
        item_id: ast::ItemId,
        item: &mut ast::Item,
    ) -> Result<(), AnalysisError> {
        match item {
            ast::Item::GlobalVar(var_def) => {
                self.visit_global_var_def(ast::GlobalVarItemId(item_id), var_def)
            }
            ast::Item::Func(func_def) => self.visit_func_def(ast::FuncItemId(item_id), func_def),
        }
    }

    /// Analyzes a global variable definition.
    fn visit_global_var_def(
        &mut self,
        _item_id: ast::GlobalVarItemId,
        var_def: &mut ast::VarDef,
    ) -> Result<(), AnalysisError> {
        self.visit_var_def(var_def, "global variable")?;
        Ok(())
    }

    /// Analyzes a local variable definition (not a function parameter).
    fn visit_local_var_def(&mut self, var_def: &mut ast::VarDef) -> Result<(), AnalysisError> {
        self.visit_var_def(var_def, "local variable")?;
        Ok(())
    }

    /// Analyzes a variable definition.
    ///
    /// This method contains code that is shared between [`Self::visit_global_var_def`] and
    /// [`Self::visit_local_var_def`].
    ///
    /// The `kind` parameter can be used to distinguish global and local vars in diagnostics.
    fn visit_var_def(
        &mut self,
        var_def: &mut ast::VarDef,
        _kind: &str,
    ) -> Result<(), AnalysisError> {
        if let Some(init) = &mut var_def.init {
            let _expr_type = self.visit_expr(init)?;
        }
        Ok(())
    }

    /// Analyzes a function definition.
    fn visit_func_def(
        &mut self,
        _item_id: ast::FuncItemId,
        func_def: &mut ast::FuncDef,
    ) -> Result<(), AnalysisError> {
        for param in &func_def.params {
            self.visit_func_param(param)?;
        }

        for stmt in &mut func_def.statements {
            self.visit_stmt(stmt)?;
        }

        Ok(())
    }

    /// Analyzes a function parameter.
    fn visit_func_param(&mut self, _param: &ast::FuncParam) -> Result<(), AnalysisError> {
        Ok(())
    }

    /// Analyzes a statement.
    fn visit_stmt(&mut self, stmt: &mut ast::Stmt) -> Result<(), AnalysisError> {
        match stmt {
            ast::Stmt::Empty => Ok(()),
            ast::Stmt::If(inner) => self.visit_if_stmt(inner),
            ast::Stmt::For(inner) => self.visit_for_stmt(inner),
            ast::Stmt::While(inner) => self.visit_while_stmt(inner, "while loop"),
            ast::Stmt::DoWhile(inner) => self.visit_while_stmt(inner, "do-while loop"),
            ast::Stmt::Return(expr) => self.visit_return_stmt(expr),
            ast::Stmt::Print(inner) => self.visit_print_stmt(inner),
            ast::Stmt::VarDef(var_def) => self.visit_local_var_def(var_def),
            ast::Stmt::Assign(assign) => {
                let _expr_type = self.visit_assign(assign)?;
                Ok(())
            }
            ast::Stmt::Call(call) => {
                let _expr_type = self.visit_call(call)?;
                Ok(())
            }
            ast::Stmt::Block(block) => self.visit_block(block),
        }
    }

    /// Analyzes a block statement.
    fn visit_block(&mut self, block: &mut ast::Block) -> Result<(), AnalysisError> {
        for stmt in &mut block.statements {
            self.visit_stmt(stmt)?;
        }
        Ok(())
    }

    /// Analyzes an `if` statement.
    fn visit_if_stmt(&mut self, stmt: &mut ast::IfStmt) -> Result<(), AnalysisError> {
        self.visit_cond_expr(&mut stmt.cond, "if")?;
        self.visit_stmt(&mut stmt.if_true)?;
        if let Some(if_false) = &mut stmt.if_false {
            self.visit_stmt(if_false)?;
        }
        Ok(())
    }

    /// Analyzes a `for` statement.
    fn visit_for_stmt(&mut self, stmt: &mut ast::ForStmt) -> Result<(), AnalysisError> {
        match &mut stmt.init {
            ast::ForInit::VarDef(var_def) => self.visit_local_var_def(var_def)?,
            ast::ForInit::Assign(assign) => {
                let _expr_type = self.visit_assign(assign)?;
            }
        }

        self.visit_cond_expr(&mut stmt.cond, "for loop")?;
        let _expr_type = self.visit_assign(&mut stmt.update)?;
        self.visit_stmt(&mut stmt.body)?;
        Ok(())
    }

    /// Analyzes a `while` or `do`-`while` statement.
    ///
    /// The `kind` parameter can be used to distinguish them in diagnostics.
    fn visit_while_stmt(
        &mut self,
        stmt: &mut ast::WhileStmt,
        kind: &str,
    ) -> Result<(), AnalysisError> {
        self.visit_cond_expr(&mut stmt.cond, kind)?;
        self.visit_stmt(&mut stmt.body)
    }

    /// Analyzes a `return` statement.
    fn visit_return_stmt(&mut self, expr: &mut Option<ast::Expr>) -> Result<(), AnalysisError> {
        if let Some(expr) = expr {
            let _expr_type = self.visit_expr(expr)?;
        }
        Ok(())
    }

    /// Analyzes a `print` statement.
    fn visit_print_stmt(&mut self, print: &mut ast::PrintStmt) -> Result<(), AnalysisError> {
        match print {
            ast::PrintStmt::String(_) => Ok(()),
            ast::PrintStmt::Expr(expr) => {
                let _expr_type = self.visit_expr(expr)?;
                Ok(())
            }
        }
    }

    /// Analyzes a call statement or expression and returns its return type.
    fn visit_call(&mut self, call: &mut ast::FuncCall) -> Result<ast::DataType, AnalysisError> {
        let resolved = self.tab.resolve(&*call.res_ident.0);

        let Ok(def) = resolved else {
            return Err(AnalysisError(format!(
                "referenced undefined symbol '{}'",
                resolved.unwrap_err().0
            )));
        };

        let def_info = self.tab[def].clone();

        let DefInfo::Func(func_info) = def_info else {
            return Err(AnalysisError(String::from("not a function")));
        };

        if func_info.param_count > call.args.len() {
            return Err(AnalysisError(String::from("to few arguments")));
        } else if func_info.param_count < call.args.len() {
            return Err(AnalysisError(String::from("to many arguments")));
        }

        for (index, expr) in call.args.iter_mut().enumerate() {
            let param = func_info.local_vars[index];
            let param_type = self.get_variable_type(param.0)?;
            let expr_type = self.visit_expr(expr)?;

            if !Self::is_compatible(param_type, expr_type) {
                return Err(AnalysisError(String::from("wrong parameter type")))
            }
        }

        Ok(func_info.return_type)
    }

    /// Analyzes an assignment statement or expression and returns its type.
    fn visit_assign(&mut self, assign: &mut ast::Assign) -> Result<ast::DataType, AnalysisError> {
        let rhs_type = self.visit_expr(&mut assign.rhs)?;

        let resolved = self.tab.resolve(&*assign.lhs.0);

        let Ok(def) = resolved else {
            return Err(AnalysisError(format!(
                "referenced undefined symbol '{}'",
                resolved.unwrap_err().0
            )));
        };

        let lhs_type = self.get_variable_type(def)?;

        if !Self::is_compatible(lhs_type, rhs_type) {
            Err(AnalysisError(String::from("assignment operands are not compatible")))
        } else {
            Ok(lhs_type)
        }
    }

    /// Analyzes the condition expression of a control flow statement, expecting
    /// a boolean type.
    ///
    /// The `kind` parameter describes the statement for diagnostics.
    fn visit_cond_expr(&mut self, expr: &mut ast::Expr, _kind: &str) -> Result<(), AnalysisError> {
        let cond_type = self.visit_expr(expr)?;

        if cond_type != DataType::Bool {
            Err(AnalysisError(String::from("expected boolean expression")))
        } else {
            Ok(())
        }
    }

    /// Analyzes an expression and returns its type.
    fn visit_expr(&mut self, expr: &mut ast::Expr) -> Result<ast::DataType, AnalysisError> {
        match expr {
            ast::Expr::BinaryOp(inner) => self.visit_bin_op_expr(inner),
            ast::Expr::UnaryMinus(inner) => self.visit_unary_minus_expr(inner),
            ast::Expr::Assign(inner) => self.visit_assign(inner),
            ast::Expr::Call(inner) => self.visit_call(inner),
            ast::Expr::Literal(literal) => Ok(literal.data_type()),
            ast::Expr::Var(res_ident) => self.visit_var_expr(res_ident),
        }
    }

    /// Analyzes a binary operator expression and returns its type.
    fn visit_bin_op_expr(
        &mut self,
        bin_op_expr: &mut ast::BinOpExpr,
    ) -> Result<ast::DataType, AnalysisError> {
        let lhs_type = self.visit_expr(&mut bin_op_expr.lhs)?;
        let rhs_type = self.visit_expr(&mut bin_op_expr.rhs)?;

        if lhs_type == DataType::Void || rhs_type == DataType::Void {
            return Err(AnalysisError(String::from("can't binop with void")));
        }

        match bin_op_expr.op {
            BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div => {
                if lhs_type == DataType::Bool || rhs_type == DataType::Bool {
                    Err(AnalysisError(String::from(
                        "binary operands are not compatible",
                    )))
                } else if lhs_type == DataType::Float || rhs_type == DataType::Float {
                    Ok(DataType::Float)
                } else {
                    Ok(DataType::Int)
                }
            }
            BinOp::LogOr | BinOp::LogAnd => {
                if lhs_type != DataType::Bool || rhs_type != DataType::Bool {
                    Err(AnalysisError(String::from(
                        "binary operands are not compatible",
                    )))
                } else {
                    Ok(DataType::Bool)
                }
            }
            BinOp::Eq | BinOp::Neq => {
                if (lhs_type == DataType::Bool || rhs_type == DataType::Bool)
                    && lhs_type != DataType::Bool
                    || rhs_type != DataType::Bool
                {
                    Err(AnalysisError(String::from(
                        "binary operands are not compatible",
                    )))
                } else {
                    Ok(DataType::Bool)
                }
            }
            BinOp::Lt | BinOp::Gt | BinOp::Leq | BinOp::Geq => {
                if lhs_type == DataType::Bool || rhs_type == DataType::Bool {
                    Err(AnalysisError(String::from(
                        "binary operands are not compatible",
                    )))
                } else {
                    Ok(DataType::Bool)
                }
            }
        }
    }

    /// Analyzes an unary minus expression and returns its type.
    fn visit_unary_minus_expr(
        &mut self,
        inner_expr: &mut ast::Expr,
    ) -> Result<ast::DataType, AnalysisError> {
        let expr_type = self.visit_expr(inner_expr)?;

        if expr_type == DataType::Void || expr_type == DataType::Bool {
            return Err(AnalysisError(String::from(
                "unary operand is not compatible",
            )));
        }

        Ok(expr_type)
    }

    /// Analyzes a variable expression and returns its type.
    fn visit_var_expr(
        &mut self,
        res_ident: &mut ast::ResIdent,
    ) -> Result<ast::DataType, AnalysisError> {
        let resolved = self.tab.resolve(&*res_ident.0);

        let Ok(def) = resolved else {
            return Err(AnalysisError(format!(
                "referenced undefined symbol '{}'",
                resolved.unwrap_err().0
            )));
        };

        let def_info = &self.tab[def];

        match def_info {
            DefInfo::Func(_) => Err(AnalysisError(String::from("not a variable"))),
            DefInfo::LocalVar(var) | DefInfo::GlobalVar(var) => Ok(var.data_type),
        }
    }
}

/// The top-level type that contains all program information that is collected during analysis.
///
/// Contains information about the main function and global variables that is required
/// for program startup, as well as the cumulative information collected for all definitions.
///
/// The structure can be accessed by the index operator. Providing a more specific
/// kind of id will return a more specific kind of result:
///
/// ```
/// use uwupreter::ast::DefId;
/// use uwupreter::analysis::*;
///
/// fn get_any(definitions: &ProgramInfo, id: DefId) -> &DefInfo {
///     &definitions[id]
/// }
///
/// fn get_func(definitions: &ProgramInfo, id: FuncDefId) -> &FuncInfo {
///     &definitions[id]
/// }
///
/// fn get_local_var(definitions: &ProgramInfo, id: LocalVarDefId) -> &VarInfo {
///     &definitions[id]
/// }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct ProgramInfo {
    pub definitions: Definitions,
    pub global_vars: Vec<ast::GlobalVarItemId>,
    pub main_func: Option<FuncDefId>,
}

impl Index<ast::DefId> for ProgramInfo {
    type Output = DefInfo;

    fn index(&self, id: ast::DefId) -> &Self::Output {
        &self.definitions[id]
    }
}

impl Index<LocalVarDefId> for ProgramInfo {
    type Output = VarInfo;

    fn index(&self, id: LocalVarDefId) -> &Self::Output {
        &self.definitions[id]
    }
}

impl Index<FuncDefId> for ProgramInfo {
    type Output = FuncInfo;

    fn index(&self, id: FuncDefId) -> &Self::Output {
        &self.definitions[id]
    }
}

/// A human-readable compile-time error.
#[derive(Debug, Clone, PartialEq)]
pub struct AnalysisError(String);

impl fmt::Display for AnalysisError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl From<symtab::DefineError> for AnalysisError {
    fn from(err: symtab::DefineError) -> Self {
        let msg = format!("duplicate definition of {} in the same scope", err.0);
        AnalysisError(msg)
    }
}

impl From<symtab::ResolveError> for AnalysisError {
    fn from(err: symtab::ResolveError) -> Self {
        let msg = format!("cannot resolve {} in this scope", err.0);
        AnalysisError(msg)
    }
}

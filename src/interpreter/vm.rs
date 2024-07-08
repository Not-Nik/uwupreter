//! This module contains the implementation of the virtual machine used for
//! interpreting the abstract syntax tree (AST) after the semantic analysis has
//! concluded.
//!
//! The virtual machine ([`VirtualMachine`]) maintains the state required for
//! interpretation, including global variables, function call stack, and return
//! data for functions. It provides methods to manage stack frames, set and
//! retrieve return values, and load/store variables.
//!
//! The module also defines the [`Variable`] and [`Value`] enums to represent
//! memory locations and the values that can be stored in them, respectively.
//! These types support type casting and conversion from AST literals.

use crate::{analysis, ast};

/// A structure representing the virtual machine for interpreting the abstract
/// syntax tree (AST).
///
/// This virtual machine maintains the global variables, function call stack,
/// and the return data for functions.
#[derive(Debug, Clone, PartialEq)]
pub struct VirtualMachine {
    /// The global frame that contains the global variables.
    global_vars: Vec<Variable>,
    /// The call stack that contains the function frames.
    ///
    /// Using a `Vec` of `Vec`s simplifies popping frames, because we
    /// don't have to store extra data to track the start of each frame.
    local_vars: Vec<Vec<Variable>>,
    /// The value that the current function is returning with, if any.
    ///
    /// - `None` means that no `return` statement was executed in the current function (yet).
    /// - `Some(`[`Variable::Uninit`]`)` means that a `return;` without value has been executed.
    /// - `Some(`[`Variable::Init`]`)` means that a `return value;` has been executed.
    return_var: Option<Variable>,
}

impl VirtualMachine {
    /// Creates a new `VirtualMachine` instance with the specified number of
    /// global variables.
    pub fn new(global_var_count: usize) -> Self {
        VirtualMachine {
            global_vars: vec![Variable::Uninit; global_var_count],
            local_vars: Vec::new(),
            return_var: None,
        }
    }

    /// Pushes a new stack frame onto the call stack.
    pub fn push_frame(&mut self, locals: Vec<Variable>) {
        self.local_vars.push(locals);
    }

    /// Pops the top stack frame off the call stack.
    pub fn pop_frame(&mut self) {
        self.local_vars.pop();
    }

    /// Checks if the current function is signaling the intent to return.
    pub fn is_returning(&self) -> bool {
        self.return_var.is_some()
    }

    /// Sets the return variable for the current function and signals intent to
    /// exit it.
    ///
    /// # Parameters
    /// - `value`: The value to set as the return value. If `None`, sets the
    ///   return variable to `Uninit`.
    ///
    /// # Panics
    /// Panics if a return value is already set.
    pub fn set_return(&mut self, value: Option<Value>) {
        assert!(
            !self.is_returning(),
            "cannot set a return value when already returning"
        );

        self.return_var = Some(value.map_or(Variable::Uninit, Variable::Init));
    }

    /// Reads and resets the return variable for the current function.
    ///
    /// # Returns
    /// The current return value, or `Uninit` if no return value is set.
    pub fn take_return(&mut self) -> Variable {
        self.return_var.take().unwrap_or(Variable::Uninit)
    }

    /// Loads from a variable.
    ///
    /// # Returns
    /// The value of the variable or `Uninit` if it was never initialized.
    ///
    /// # Panics
    /// Panics if attempting to load a local variable outside a function or if
    /// attempting to read the value of a function.
    pub fn load_var(&self, info: &analysis::DefInfo) -> Variable {
        match info {
            analysis::DefInfo::GlobalVar(info) => &self.global_vars[info.offset],

            analysis::DefInfo::LocalVar(info) => &self
                .local_vars
                .last()
                .expect("attempted to load local variable outside of function")[info.offset],

            analysis::DefInfo::Func(_) => unreachable!("attempted to read the value of a function"),
        }
        .clone()
    }

    /// Casts a value to the type of a variable and stores the cast result in the variable.
    ///
    /// # Parameters
    /// - `info`: Information about the variable to store.
    /// - `value`: The value to store in the variable.
    ///
    /// # Returns
    /// The value that was stored, cast to the [`DataType`](ast::DataType) of
    /// the variable type.
    ///
    /// # Panics
    /// Panics if attempting to store a value in a function or referring to a
    /// local variable from the global scope.
    pub fn store_var(&mut self, info: &analysis::DefInfo, value: Value) -> Value {
        // locate the variable in the global or local variable stack
        let (variable, data_type) = match info {
            analysis::DefInfo::GlobalVar(info) => {
                (&mut self.global_vars[info.offset], info.data_type)
            }

            analysis::DefInfo::LocalVar(info) => (
                &mut self
                    .local_vars
                    .last_mut()
                    .expect("attempted to write into a local variable outside of function")
                    [info.offset],
                info.data_type,
            ),

            analysis::DefInfo::Func(_) => {
                unreachable!("attempted to write a value into a function")
            }
        };

        // convert the value into the target type and return its copy
        let value = value.cast(data_type);
        *variable = Variable::Init(value.clone());
        value
    }
}

/// A memory location. This represents a (global or local) variable
/// that may or may not be initialized with a [`Value`].
#[derive(Debug, Clone, PartialEq)]
pub enum Variable {
    // An uninitialized variable.
    Uninit,
    // An initialized variable.
    Init(Value),
}

/// The values that can be stored in [Variables](Variable).
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Int(i64),
    Float(f64),
    Bool(bool),
}

impl Value {
    /// Returns the data type of the value.
    pub fn data_type(&self) -> ast::DataType {
        match self {
            Value::Int(_) => ast::DataType::Int,
            Value::Float(_) => ast::DataType::Float,
            Value::Bool(_) => ast::DataType::Bool,
        }
    }

    /// Casts the value to the specified data type.
    ///
    /// # Panics
    /// Panics if the cast is invalid, which should have been caught during the
    /// semantic analysis.
    #[allow(clippy::cast_precision_loss)] // casting (i64 -> f64) loses precision
    pub fn cast(self, target_type: ast::DataType) -> Self {
        match (self, target_type) {
            (from, into) if from.data_type() == into => from,
            (Value::Int(from), ast::DataType::Float) => Value::Float(from as f64),
            (from, into) => unreachable!("unsupported cast from `{from:?}` to `{into:?}`"),
        }
    }
}

/// Converts an AST literal to a value.
///
/// Using the `From` trait indicates that this conversion is lossless.
impl From<ast::Literal> for Value {
    fn from(literal: ast::Literal) -> Self {
        match literal {
            ast::Literal::Int(value) => Value::Int(value),
            ast::Literal::Float(value) => Value::Float(value),
            ast::Literal::Bool(value) => Value::Bool(value),
        }
    }
}

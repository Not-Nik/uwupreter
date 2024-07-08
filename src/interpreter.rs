//! The interpreter that executes C1 programs.
//!
//! This module contains the implementation of the interpreter that uses the
//! abstract syntax tree (AST) as well as the information calculated during
//! the semantic analysis to run a C1 program.
//!
//! It utilizes a virtual machine ([`VirtualMachine`]) helper to maintain the
//! state required for interpreting the AST, including managing global variables,
//! the function call stack (including local variables), and return values.
//!
//! The entry point for interpretation is the [`interpret`] function, which
//! initializes the interpreter, sets up global variables, and visits the main
//! function of the program.
//!
//! The module also defines the [`Interpreter`] structure, which provides
//! methods to visit and evaluate statements and expressions in the AST, handle
//! function calls, and manage control flow constructs such as loops and
//! conditionals.
//!
//! Additionally, the module defines the [`InterpretError`] structure for
//! communicating errors that occur during interpretation.

#![allow(dead_code)]

use crate::ast::{BinOp, Expr, ForInit, Stmt};
use crate::{analysis, ast};
use std::fmt::{self, Write};
use std::ops::Index;
use vm::{Value, Variable, VirtualMachine};
use crate::analysis::DefInfo;
use crate::ast::DataType::{Float, Void};

mod vm;

/// The entry function of the interpretation.
///
/// This function initializes the interpreter with the given AST and program
/// information, sets up the global variables, and visits the main function.
pub fn interpret(
    ast: &ast::Program,
    info: &analysis::ProgramInfo,
) -> Result<String, InterpretError> {
    let mut interpreter = Interpreter {
        ast,
        info,
        output: String::new(),
        vm: VirtualMachine::new(info.global_vars.len()),
    };

    // initialize the global variables in declaration order
    for &item_id in &info.global_vars {
        interpreter.visit_var_def(&ast[item_id])?;
    }

    // visit the main function
    let mut res_ident = ast::ResIdent::new(ast::Ident("main".to_owned()));
    res_ident.set_res(info.main_func.unwrap().0);
    interpreter.visit_func_call(&ast::FuncCall {
        res_ident,
        args: Vec::new(),
    })?;

    // return the resulting output
    Ok(interpreter.output)
}

/// Computes the *least upper bound* (LUB) of two types.
///
/// Given two types `a` and `b`, the LUB is a type `c`, such that
/// - both `a` and `b` can be cast to `c`, and
/// - `c` is the *most concrete* type that satisfies this property.
fn least_upper_bound(lhs: ast::DataType, rhs: ast::DataType) -> ast::DataType {
    use ast::DataType::*;
    match (lhs, rhs) {
        (a, b) if a == b => a,
        (Int, Float) | (Float, Int) => Float,
        (a, b) => unreachable!("invalid LUB of `{a:?}` and `{b:?}`"),
    }
}

/// Structure representing the interpreter.
///
/// This structure holds the state required for interpreting the AST, including
/// the AST, program information, output string, and the virtual machine storing
/// the variables.
#[derive(Debug, Clone, PartialEq)]
struct Interpreter<'a> {
    ast: &'a ast::Program,
    info: &'a analysis::ProgramInfo,
    output: String,
    vm: VirtualMachine,
}

impl Interpreter<'_> {
    /// Visits a statement.
    fn visit_stmt(&mut self, stmt: &ast::Stmt) -> Result<(), InterpretError> {
        use ast::Stmt::*;
        match stmt {
            Empty => Ok(()),
            If(inner) => self.visit_if_stmt(inner),
            For(inner) => self.visit_for_stmt(inner),
            While(inner) => self.visit_while_stmt(inner),
            DoWhile(inner) => self.visit_do_while_stmt(inner),
            Return(expr) => self.visit_return_stmt(expr),
            Print(inner) => self.visit_print_stmt(inner),
            VarDef(var_def) => self.visit_var_def(var_def),
            Assign(assign) => self.visit_assign(assign).map(|_| ()),
            Call(call) => self.visit_func_call(call).map(|_| ()),
            Block(block) => self.visit_block(block),
        }
    }

    /// Visits an expression and evaluates it.
    fn visit_expr(&mut self, expr: &ast::Expr) -> Result<Value, InterpretError> {
        use ast::Expr::*;
        match expr {
            BinaryOp(inner) => self.visit_bin_op_expr(inner),
            UnaryMinus(inner) => self.visit_unary_minus(inner),
            Assign(assign) => self.visit_assign(assign),
            Call(inner) => self.visit_func_call_expr(inner),
            Literal(literal) => Ok(literal.clone().into()),
            Var(res_ident) => self.visit_load_var(res_ident),
        }
    }

    /// Visits an `if` statement.
    fn visit_if_stmt(&mut self, stmt: &ast::IfStmt) -> Result<(), InterpretError> {
        let cond = self.visit_expr(&stmt.cond)?;

        let Value::Bool(cond_bool) = cond else {
            return Err(InterpretError(String::from("invalid if condition")));
        };

        if cond_bool {
            self.visit_stmt(&stmt.if_true)?;
        } else {
            if let Some(else_stmt) = &stmt.if_false {
                self.visit_stmt(else_stmt.as_ref())?;
            }
        }

        Ok(())
    }

    /// Visits a `for` statement.
    fn visit_for_stmt(&mut self, stmt: &ast::ForStmt) -> Result<(), InterpretError> {
        self.visit_stmt(&match &stmt.init {
            ForInit::VarDef(var) => Stmt::VarDef(var.clone()),
            ForInit::Assign(ass) => Stmt::Assign(ass.clone()),
        })?;

        loop {
            let cond = self.visit_expr(&stmt.cond)?;

            let Value::Bool(cond_bool) = cond else {
                return Err(InterpretError(String::from("invalid if condition")));
            };

            if !cond_bool {
                break;
            }

            self.visit_stmt(&stmt.body)?;

            if self.vm.is_returning() {
                break;
            }

            self.visit_stmt(&Stmt::Assign(stmt.update.clone()))?;
        }

        Ok(())
    }

    /// Visits a `while` statement.
    fn visit_while_stmt(&mut self, stmt: &ast::WhileStmt) -> Result<(), InterpretError> {
        loop {
            if self.vm.is_returning() {
                break;
            }

            let cond = self.visit_expr(&stmt.cond)?;

            let Value::Bool(cond_bool) = cond else {
                return Err(InterpretError(String::from("invalid if condition")));
            };

            if !cond_bool {
                break;
            }

            self.visit_stmt(&stmt.body)?;
        }

        Ok(())
    }

    /// Visits a `do-while` statement.
    fn visit_do_while_stmt(&mut self, stmt: &ast::WhileStmt) -> Result<(), InterpretError> {
        loop {
            self.visit_stmt(&stmt.body)?;

            if self.vm.is_returning() {
                break;
            }

            let cond = self.visit_expr(&stmt.cond)?;

            let Value::Bool(cond_bool) = cond else {
                return Err(InterpretError(String::from("invalid if condition")));
            };

            if !cond_bool {
                break;
            }
        }

        Ok(())
    }

    /// Visits a `return` statement, setting the return value.
    fn visit_return_stmt(&mut self, expr: &Option<ast::Expr>) -> Result<(), InterpretError> {
        if let Some(ret) = &expr {
            let ret_val = self.visit_expr(ret)?;
            self.vm.set_return(Some(ret_val));
        } else {
            self.vm.set_return(None);
        }
        Ok(())
    }

    /// Visits a `print` statement, writing into the output string.
    fn visit_print_stmt(&mut self, print: &ast::PrintStmt) -> Result<(), InterpretError> {
        match print {
            ast::PrintStmt::String(string) => {
                writeln!(self.output, "{string}").unwrap();
            }
            ast::PrintStmt::Expr(expr) => {
                let value = self.visit_expr(expr)?;

                match value {
                    Value::Int(int) => writeln!(self.output, "{int}").unwrap(),
                    Value::Float(float) => {
                        let plain = format!("{}", float);
                        let trunc = format!("{:.0}", float);

                        let (decimal, scientific) = if plain.len() == trunc.len() {
                            (format!("{:.1}", float), format!("{:e}.0", float))
                        } else {
                            (format!("{}", float), format!("{:e}", float))
                        };

                        if decimal.len() <= scientific.len() {
                            writeln!(self.output, "{}", decimal.to_lowercase()).unwrap()
                        } else {
                            writeln!(self.output, "{scientific}").unwrap()
                        }
                    },
                    Value::Bool(boolean) => writeln!(self.output, "{boolean}").unwrap(),
                }
            }
        }
        Ok(())
    }

    /// Visits a variable definition and initializes it if possible.
    fn visit_var_def(&mut self, var_def: &ast::VarDef) -> Result<(), InterpretError> {
        let def = self.info.definitions.index(var_def.res_ident.get_res());
        if let Some(init) = &var_def.init {
            let value = self.visit_expr(init)?;
            self.vm.store_var(def, value);
        }

        Ok(())
    }

    /// Visits a block of statements and evaluates each one.
    fn visit_block(&mut self, block: &ast::Block) -> Result<(), InterpretError> {
        for stmt in &block.statements {
            self.visit_stmt(stmt)?;
            if self.vm.is_returning() {
                break;
            }
        }

        Ok(())
    }

    /// Visits a function call and evaluates it.
    fn visit_func_call(&mut self, call: &ast::FuncCall) -> Result<Variable, InterpretError> {
        let def_id = call.res_ident.get_res();
        let func_info = match &self.info.definitions[def_id] {
            analysis::DefInfo::Func(info) => info,
            _ => unreachable!("function call resolves to non-function"),
        };
        let func_def = &self.ast[func_info.item_id];

        let mut args = Vec::with_capacity(call.args.len());

        for (arg, param) in call.args.iter().zip(func_info.local_vars.iter()) {
            let value = self.visit_expr(arg)?;
            args.push(match value {
                Value::Int(i) => {
                    let info = &self.info.definitions[param.0];
                    let DefInfo::LocalVar(var) = info else {
                        return Err(InterpretError(String::from("invalid param")));
                    };
                    if var.data_type == Float {
                        Value::Float(i as f64)
                    } else {
                        Value::Int(i)
                    }
                }
                Value::Float(f) => Value::Float(f),
                Value::Bool(b) => Value::Bool(b),
            });
        }

        let mut variables: Vec<Variable> =
            args.into_iter().map(|val| Variable::Init(val)).collect();
        variables.extend(func_info.local_vars.iter().map(|_| Variable::Uninit));

        self.vm.push_frame(variables);

        // Evaluate the function body.
        for stmt in &func_def.statements {
            self.visit_stmt(stmt)?;
            if self.vm.is_returning() {
                break;
            }
        }

        self.vm.pop_frame();

        if func_info.return_type != Void && !self.vm.is_returning() {
            Err(InterpretError(String::from("implicit return from non-void function")))
        } else {
            let value = self.vm.take_return();
            match value {
                Variable::Uninit => {
                    Ok(Variable::Uninit)
                }
                Variable::Init(i) => {
                    match i {
                        Value::Int(i) => {
                            if func_info.return_type == Float {
                                Ok(Variable::Init(Value::Float(i as f64)))
                            } else {
                                Ok(Variable::Init(Value::Int(i)))
                            }
                        }
                        Value::Float(f) => Ok(Variable::Init(Value::Float(f))),
                        Value::Bool(b) => Ok(Variable::Init(Value::Bool(b))),
                    }
                }
            }
        }
    }

    /// Visits a binary operation expression and evaluates it.
    fn visit_bin_op_expr(&mut self, bin_op_expr: &ast::BinOpExpr) -> Result<Value, InterpretError> {
        let left_val = self.visit_expr(&bin_op_expr.lhs)?;
        let right_val = self.visit_expr(&bin_op_expr.rhs)?;

        let overflow = InterpretError(String::from("overflow"));
        let zero_division = InterpretError(String::from("zero division"));
        let invalid_operand = InterpretError(String::from("invalid operand"));

        let res = match bin_op_expr.op {
            BinOp::Add => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => Value::Int(int.checked_add(int2).ok_or(overflow)?),
                    Value::Float(float2) => Value::Float(int as f64 + float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => Value::Float(float + int2 as f64),
                    Value::Float(float2) => Value::Float(float + float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(_) => unreachable!(),
            },
            BinOp::Sub => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => Value::Int(int.checked_sub(int2).ok_or(overflow)?),
                    Value::Float(float2) => Value::Float(int as f64 - float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => Value::Float(float - int2 as f64),
                    Value::Float(float2) => Value::Float(float - float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(_) => unreachable!(),
            },
            BinOp::Mul => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => Value::Int(int.checked_mul(int2).ok_or(overflow)?),
                    Value::Float(float2) => Value::Float(int as f64 * float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => Value::Float(float * int2 as f64),
                    Value::Float(float2) => Value::Float(float * float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(_) => unreachable!(),
            },
            BinOp::Div => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => {
                        if int2 == 0 {
                            return Err(zero_division);
                        }
                        Value::Int(int.checked_div(int2).ok_or(overflow)?)
                    }
                    Value::Float(float2) => {
                        Value::Float(int as f64 / float2)
                    }
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => {
                        Value::Float(float / int2 as f64)
                    }
                    Value::Float(float2) => {
                        Value::Float(float / float2)
                    }
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(_) => unreachable!(),
            },
            BinOp::LogOr => {
                let Value::Bool(left_bool) = left_val else {
                    return Err(invalid_operand);
                };
                let Value::Bool(right_bool) = right_val else {
                    return Err(invalid_operand);
                };
                Value::Bool(left_bool || right_bool)
            }
            BinOp::LogAnd => {
                let Value::Bool(left_bool) = left_val else {
                    return Err(invalid_operand);
                };
                let Value::Bool(right_bool) = right_val else {
                    return Err(invalid_operand);
                };
                Value::Bool(left_bool && right_bool)
            }
            BinOp::Eq => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => Value::Bool(int == int2),
                    Value::Float(float2) => Value::Bool(int as f64 == float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => Value::Bool(float == int2 as f64),
                    Value::Float(float2) => Value::Bool(float == float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(boolean) => {
                    let Value::Bool(right_bool) = right_val else {
                        return Err(invalid_operand);
                    };
                    Value::Bool(boolean == right_bool)
                }
            },
            BinOp::Neq => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => Value::Bool(int != int2),
                    Value::Float(float2) => Value::Bool(int as f64 != float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => Value::Bool(float != int2 as f64),
                    Value::Float(float2) => Value::Bool(float != float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(boolean) => {
                    let Value::Bool(right_bool) = right_val else {
                        return Err(invalid_operand);
                    };
                    Value::Bool(boolean != right_bool)
                }
            },
            BinOp::Lt => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => Value::Bool(int < int2),
                    Value::Float(float2) => Value::Bool((int as f64) < float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => Value::Bool(float < int2 as f64),
                    Value::Float(float2) => Value::Bool(float < float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(boolean) => {
                    let Value::Bool(right_bool) = right_val else {
                        return Err(invalid_operand);
                    };
                    Value::Bool(boolean < right_bool)
                }
            },
            BinOp::Gt => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => Value::Bool(int > int2),
                    Value::Float(float2) => Value::Bool(int as f64 > float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => Value::Bool(float > int2 as f64),
                    Value::Float(float2) => Value::Bool(float > float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(boolean) => {
                    let Value::Bool(right_bool) = right_val else {
                        return Err(invalid_operand);
                    };
                    Value::Bool(boolean > right_bool)
                }
            },
            BinOp::Leq => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => Value::Bool(int <= int2),
                    Value::Float(float2) => Value::Bool(int as f64 <= float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => Value::Bool(float <= int2 as f64),
                    Value::Float(float2) => Value::Bool(float <= float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(boolean) => {
                    let Value::Bool(right_bool) = right_val else {
                        return Err(invalid_operand);
                    };
                    Value::Bool(boolean <= right_bool)
                }
            },
            BinOp::Geq => match left_val {
                Value::Int(int) => match right_val {
                    Value::Int(int2) => Value::Bool(int >= int2),
                    Value::Float(float2) => Value::Bool(int as f64 >= float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Float(float) => match right_val {
                    Value::Int(int2) => Value::Bool(float >= int2 as f64),
                    Value::Float(float2) => Value::Bool(float >= float2),
                    Value::Bool(_) => unreachable!(),
                },
                Value::Bool(boolean) => {
                    let Value::Bool(right_bool) = right_val else {
                        return Err(invalid_operand);
                    };
                    Value::Bool(boolean >= right_bool)
                }
            },
        };
        Ok(res)
    }

    /// Visits a unary minus expression and evaluates it.
    fn visit_unary_minus(&mut self, inner_expr: &ast::Expr) -> Result<Value, InterpretError> {
        let value = self.visit_expr(inner_expr)?;

        Ok(match value {
            Value::Int(int) => Value::Int(
                int.checked_neg()
                    .ok_or(InterpretError(String::from("overflow")))?,
            ),
            Value::Float(float) => Value::Float(float * -1.0f64),
            Value::Bool(_) => unreachable!(),
        })
    }

    /// Visits an assignment expression and evaluates it.
    fn visit_assign(&mut self, assign: &ast::Assign) -> Result<Value, InterpretError> {
        let value = self.visit_expr(&assign.rhs)?;
        let def = self.info.definitions.index(assign.lhs.get_res());
        Ok(self.vm.store_var(def, value))
    }

    /// Visits a function call expression and evaluates it.
    fn visit_func_call_expr(&mut self, call: &ast::FuncCall) -> Result<Value, InterpretError> {
        let value = self.visit_func_call(call)?;
        match value {
            Variable::Uninit => Err(InterpretError(String::from("void result"))),
            Variable::Init(v) => Ok(v),
        }
    }

    /// Visits a variable and loads its value.
    fn visit_load_var(&mut self, ident: &ast::ResIdent) -> Result<Value, InterpretError> {
        let def = self.info.definitions.index(ident.get_res());
        let value = self.vm.load_var(def);

        match value {
            Variable::Uninit => Err(InterpretError(String::from("uninitialised variable"))),
            Variable::Init(v) => Ok(v),
        }
    }
}

/// Structure representing an interpretation error.
///
/// This structure holds a human-readable error message string.
#[derive(Debug, Clone, PartialEq)]
pub struct InterpretError(String);

impl fmt::Display for InterpretError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

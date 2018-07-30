//! Simple analyses applied to the AST as a to verify basic correctness

use std::error;
use std::fmt;

use ast::{Pos, Statement, StatementKind};
use ast_walker::{visit_statements, StatementVisitor, BlockType};

#[derive(Debug)]
pub enum CompileError {
    UnexpectedReturn(Pos),
    UnexpectedLoopControl(Pos),
}

impl error::Error for CompileError {}

impl fmt::Display for CompileError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CompileError::UnexpectedReturn(..) => {
                write!(f, "Unexpected return statement")
            }
            CompileError::UnexpectedLoopControl(..) => {
                write!(f, "Unexpected loop control statement")
            }
        }
    }
}

pub fn verify_control_flow(program: &[Statement]) -> Result<(), CompileError> {
    visit_statements(program, &mut ControlFlowVerifier::new())
}

#[derive(Default)]
struct ExecutionContext {
    is_func: bool,
    loop_depth: usize,
}

struct ControlFlowVerifier {
    exec_ctxs: Vec<ExecutionContext>,
}

impl ControlFlowVerifier {
    fn new() -> Self {
        ControlFlowVerifier {
            exec_ctxs: vec![ExecutionContext::default()],
        }
    }

    fn ctx(&self) -> &ExecutionContext {
        self.exec_ctxs.last().expect("exec ctx")
    }

    fn ctx_mut(&mut self) -> &mut ExecutionContext {
        self.exec_ctxs.last_mut().expect("exec ctx")
    }

    fn is_func_body(&self) -> bool {
        self.ctx().is_func
    }

    fn is_loop(&self) -> bool {
        self.ctx().loop_depth > 0
    }
}

impl StatementVisitor for ControlFlowVerifier {
    type Error = CompileError;

    fn visit_statement(&mut self, statement: &Statement)
        -> Result<(), Self::Error>
    {
        match statement.kind {
            StatementKind::Return(..) if !self.is_func_body() => {
                Err(CompileError::UnexpectedReturn(statement.pos))
            }
            StatementKind::Continue | StatementKind::Break if !self.is_loop() => {
                Err(CompileError::UnexpectedLoopControl(statement.pos))
            }
            _ => Ok(())
        }
    }

    fn enter_block(&mut self, block_type: BlockType, _: &Statement)
        -> Result<(), Self::Error>
    {
        match block_type {
            BlockType::LoopBlock => self.ctx_mut().loop_depth += 1,
            BlockType::FuncBodyBlock => {
                let mut new_ctx = ExecutionContext::default();
                new_ctx.is_func = true;
                self.exec_ctxs.push(new_ctx);
            }
            BlockType::IfBlock | BlockType::ElseBlock => {}
        }

        Ok(())
    }

    fn exit_block(&mut self, block_type: BlockType, _: &Statement)
        -> Result<(), Self::Error>
    {
        match block_type {
            BlockType::LoopBlock => self.ctx_mut().loop_depth -= 1,
            BlockType::FuncBodyBlock => { self.exec_ctxs.pop(); },
            BlockType::IfBlock | BlockType::ElseBlock => {}
        }

        Ok(())
    }
}

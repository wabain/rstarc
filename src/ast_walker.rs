use ast::{Statement, StatementKind};

#[derive(Debug, PartialEq)]
pub enum BlockType {
    LoopBlock,
    FuncBodyBlock,
    IfBlock,
    ElseBlock,
}

pub fn visit_statements<'prog, V>(statements: &'prog [Statement],
                                  visitor: &mut V) -> Result<(), V::Error>
    where V: StatementVisitor<'prog>
{
    for statement in statements {
        visitor.visit_statement(statement)?;

        match &statement.kind {
            StatementKind::While(_, block) | StatementKind::Until(_, block) => {
                visitor.enter_block(BlockType::LoopBlock, statement)?;
                visit_statements(block, visitor)?;
                visitor.exit_block(BlockType::LoopBlock, statement)?;
            }
            StatementKind::Condition(_, if_block, else_block) => {
                visitor.enter_block(BlockType::IfBlock, statement)?;
                visit_statements(if_block, visitor)?;
                visitor.exit_block(BlockType::IfBlock, statement)?;

                visitor.enter_block(BlockType::ElseBlock, statement)?;
                visit_statements(else_block, visitor)?;
                visitor.exit_block(BlockType::ElseBlock, statement)?;
            }
            StatementKind::FuncDef(_, _, body) => {
                visitor.enter_block(BlockType::FuncBodyBlock, statement)?;
                visit_statements(body, visitor)?;
                visitor.exit_block(BlockType::FuncBodyBlock, statement)?;
            }
            _ => {}
        }
    }

    Ok(())
}

pub trait StatementVisitor<'prog> {
    type Error;

    fn visit_statement(&mut self, &'prog Statement) -> Result<(), Self::Error>;

    fn enter_block(&mut self, _: BlockType, _: &'prog Statement)
        -> Result<(), Self::Error>
    {
        Ok(())
    }

    fn exit_block(&mut self, _: BlockType, _: &'prog Statement)
        -> Result<(), Self::Error>
    {
        Ok(())
    }
}

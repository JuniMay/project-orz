use std::fmt::Write;

use thiserror::Error;

use super::{layout::OpList, parse::ParseState, symbol::NameAllocDuplicatedErr, value::Value};
use crate::{
    core::parse::{ParseErrorKind, TokenKind},
    delimiter,
    parse_error,
    support::{
        error::{PrintResult, VerifyResult},
        storage::ArenaPtr,
    },
    token_wildcard,
    verify_error,
    Context,
    OpObj,
    Parse,
    ParseResult,
    Print,
    PrintState,
    Region,
    RunVerifiers,
    TyObj,
    Typed,
    Verify,
};

/// The block in the region.
pub struct Block {
    /// Self ptr.
    self_ptr: ArenaPtr<Self>,
    /// Arguments of the block.
    ///
    /// There is no phi node in the OrzIR, instead, the block arguments are used
    /// to deal with the incoming values from the predecessors and keep the IR
    /// in the SSA form.
    args: Vec<ArenaPtr<Value>>,
    /// If this block is an entry block.
    ///
    /// An entry block can be omitted if it has no arguments. The entry block
    /// must be the first block in the layout.
    is_entry: bool,
    /// The parent region.
    parent_region: ArenaPtr<Region>,
    /// The layout of the block.
    ///
    /// The layout is the list of operations in the block, indicating the print
    /// order of the operations.
    layout: OpList,
}

impl RunVerifiers for Block {
    fn run_verifiers(&self, _ctx: &Context) -> VerifyResult<()> { Ok(()) }
}

/// The error when the entry block is not the first block in the layout.
#[derive(Debug, Error)]
#[error("The entry block must be the first block in the layout.")]
pub struct InvalidEntryBlockError;

impl Verify for Block {
    fn verify(&self, ctx: &Context) -> VerifyResult<()> {
        if self.is_entry {
            let parent_region = self.parent_region.deref(&ctx.regions);
            if parent_region.layout().front().unwrap() != self.self_ptr {
                return verify_error!(InvalidEntryBlockError).into();
            }
        }

        for arg in &self.args {
            arg.deref(&ctx.values).verify(ctx)?;
        }
        for op in self.layout().iter() {
            op.deref(&ctx.ops).as_ref().verify(ctx)?;
        }
        Ok(())
    }
}

impl Block {
    /// Create a new block.
    pub fn new(
        ctx: &mut Context,
        is_entry: bool,
        parent_region: ArenaPtr<Region>,
        name: Option<String>,
    ) -> ArenaPtr<Block> {
        let self_ptr = if let Some(name) = name {
            let self_ptr = parent_region
                .deref(&ctx.regions)
                .block_names
                .borrow()
                .get_by_name(&name)
                .unwrap_or_else(|| ctx.blocks.reserve());
            parent_region
                .deref(&ctx.regions)
                .block_names
                .borrow_mut()
                .set(self_ptr, name)
                .unwrap();
            self_ptr
        } else {
            ctx.blocks.reserve()
        };
        let instance = Self {
            self_ptr,
            args: Vec::new(),
            is_entry,
            parent_region,
            layout: OpList::default(),
        };
        ctx.blocks.fill(self_ptr, instance);
        self_ptr
    }

    /// Get the layout of operations in the block.
    pub fn layout(&self) -> &OpList { &self.layout }

    /// Get the mutable layout of operations in the block.
    pub fn layout_mut(&mut self) -> &mut OpList { &mut self.layout }

    /// Get the name of the block.
    ///
    /// This will allocate a new name if the block does not have one.
    pub fn name(&self, ctx: &Context) -> String {
        let region = self.parent_region.deref(&ctx.regions);
        let name = region.block_names.borrow_mut().get(self.self_ptr);
        name
    }

    /// Set the name of the block.
    pub fn set_name(&self, ctx: &Context, name: String) -> Result<(), NameAllocDuplicatedErr> {
        let region = self.parent_region.deref(&ctx.regions);
        region.block_names.borrow_mut().set(self.self_ptr, name)
    }

    /// Set the arguments of the block by the given index.
    pub fn set_arg(&mut self, index: usize, arg: ArenaPtr<Value>) -> Option<ArenaPtr<Value>> {
        if index > self.args.len() {
            panic!("index out of range when setting block argument.");
        }
        if index == self.args.len() {
            self.args.push(arg);
            return None;
        }

        let old = std::mem::replace(&mut self.args[index], arg);
        Some(old)
    }

    /// Get the number of arguments of the block.
    pub fn num_args(&self) -> usize { self.args.len() }

    /// Get the arguments of the block.
    pub fn args(&self) -> &[ArenaPtr<Value>] { &self.args }

    /// Test if the block is an entry block.
    pub fn is_entry(&self) -> bool { self.is_entry }

    /// Reserve a unknown block with a name, if the name is already used, return
    /// the block.
    pub(crate) fn reserve_with_name(
        ctx: &mut Context,
        name: String,
        region: ArenaPtr<Region>,
    ) -> ArenaPtr<Block> {
        let region = region.deref(&ctx.regions);
        let self_ptr = region
            .block_names
            .borrow()
            .get_by_name(&name)
            .unwrap_or_else(|| ctx.blocks.reserve());
        region.block_names.borrow_mut().set(self_ptr, name).unwrap();
        self_ptr
    }

    /// Get the parent region of the block.
    pub fn parent_region(&self) -> ArenaPtr<Region> { self.parent_region }
}

impl Parse for Block {
    type Item = ArenaPtr<Block>;

    /// Parsing a block.
    ///
    /// A block starts with a block label `^...`, and an optional list of block
    /// arguments. A block ends with the `}` token, which indicates the end of a
    /// region, or another block label.
    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.peek()?;
        let block = match &token.kind {
            TokenKind::BlockLabel(_) => {
                let token = state.stream.consume()?;
                if let TokenKind::BlockLabel(label) = token.kind {
                    Block::new(ctx, false, state.curr_region(), Some(label))
                } else {
                    unreachable!()
                }
            }
            _ => Block::new(ctx, true, state.curr_region(), None),
        };

        // parse the block arguments.
        let is_entry = block.deref(&ctx.blocks).is_entry();
        if !is_entry {
            let token = state.stream.consume()?;
            match token.kind {
                TokenKind::Char('(') => {
                    let mut cnt = 0;
                    // parse the arguments.
                    loop {
                        let token = state.stream.peek()?;
                        match &token.kind {
                            TokenKind::Char(')') => {
                                state.stream.consume()?;
                                break;
                            }
                            TokenKind::ValueName(name) => {
                                let name = name.clone();
                                let _arg = Value::parse(ctx, state)?;

                                state.stream.expect(delimiter!(':'))?;
                                let ty = TyObj::parse(ctx, state)?;

                                let arg =
                                    Value::new_block_argument(ctx, ty, block, cnt, Some(name));
                                block.deref_mut(&mut ctx.blocks).set_arg(cnt, arg);

                                cnt += 1;

                                if state.stream.consume_if(TokenKind::Char(','))?.is_none() {
                                    // end of the arguments.
                                    state.stream.expect(delimiter!(')'))?;
                                    break;
                                }
                            }
                            _ => {
                                return parse_error!(
                                    token.span,
                                    ParseErrorKind::InvalidToken(
                                        vec![delimiter!(')'), token_wildcard!("%...")].into(),
                                        token.kind.clone()
                                    )
                                )
                                .into();
                            }
                        }
                    }
                    state.stream.expect(delimiter!(':'))?;
                }
                TokenKind::Char(':') => {
                    // just exit.
                }
                _ => {
                    return parse_error!(
                        token.span,
                        ParseErrorKind::InvalidToken(
                            vec![delimiter!('('), delimiter!(':')].into(),
                            token.kind
                        )
                    )
                    .into();
                }
            }
        }

        state.enter_op_from(block);

        // parse the operations.
        loop {
            let token = state.stream.peek()?;
            match token.kind {
                TokenKind::ValueName(_) | TokenKind::Tokenized(_) => {
                    // parse an operation
                    let op = OpObj::parse(ctx, state)?;
                    block
                        .deref_mut(&mut ctx.blocks)
                        .layout_mut()
                        .append(op)
                        .expect("should be able to append an operation when parsing.")
                }
                TokenKind::BlockLabel(_) | TokenKind::Char('}') => {
                    // end of the block
                    break;
                }
                _ => {
                    return parse_error!(
                        token.span,
                        ParseErrorKind::InvalidToken(
                            vec![
                                delimiter!('}'),
                                token_wildcard!("%..."),
                                token_wildcard!("^..."),
                                token_wildcard!("...")
                            ]
                            .into(),
                            token.kind.clone()
                        )
                    )
                    .into();
                }
            }
        }

        state.exit_op();

        Ok(block)
    }
}

impl Print for Block {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        if !self.is_entry() {
            state.write_indent()?;
            write!(state.buffer, "^{}", self.name(ctx))?;
            if self.args.is_empty() {
                write!(state.buffer, ":")?;
            } else {
                write!(state.buffer, "(")?;
                for (i, arg) in self.args.iter().enumerate() {
                    let arg = arg.deref(&ctx.values);
                    arg.print(ctx, state)?;
                    write!(state.buffer, ": ")?;
                    let ty = arg.ty(ctx);
                    ty.deref(&ctx.tys).print(ctx, state)?;
                    if i != self.args.len() - 1 {
                        write!(state.buffer, ", ")?;
                    }
                }
                write!(state.buffer, "):")?;
            }
            writeln!(state.buffer)?;
        }

        state.indent();
        for op in self.layout().iter() {
            state.write_indent()?;
            op.deref(&ctx.ops).print(ctx, state)?;
            writeln!(state.buffer)?;
        }
        state.dedent();

        Ok(())
    }
}

use std::fmt::Write;

use super::context::Context;
use crate::PrintResult;

pub struct PrintState {
    indent: &'static str,
    curr_indent: u32,
    pub buffer: String,
}

impl PrintState {
    pub fn new(indent: &'static str) -> Self {
        Self {
            indent,
            curr_indent: 0,
            buffer: String::new(),
        }
    }

    /// Indent the current line.
    pub fn indent(&mut self) { self.curr_indent += 1; }

    /// Dedent the current line.
    pub fn dedent(&mut self) { self.curr_indent -= 1; }

    /// Write the current indent.
    pub fn write_indent(&mut self) -> std::fmt::Result {
        for _ in 0..self.curr_indent {
            write!(self.buffer, "{}", self.indent)?;
        }
        Ok(())
    }
}

pub trait Print {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()>;
}

impl<T: Print> Print for Option<T> {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> PrintResult<()> {
        if let Some(inner) = self {
            inner.print(ctx, state)?;
        }
        Ok(())
    }
}

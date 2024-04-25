use std::{collections::HashMap, fmt::Write};

use thiserror::Error;

use super::op::OpObj;
use crate::{
    parse_error,
    support::bimap::{BiMap, Duplicated},
    token_wildcard,
    ArenaPtr,
    Context,
    Parse,
    ParseErrorKind,
    ParseResult,
    ParseState,
    Print,
    PrintResult,
    PrintState,
    Region,
    TokenKind,
};

/// A symbol.
///
/// This is currently a simple wrapper around a string, just with implementation
/// of [Parse] and [Print].
#[derive(Debug, Default, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct Symbol(String);

impl Parse for Symbol {
    type Item = Self;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::SymbolName(name) = token.kind {
            let op = state.curr_op();
            // register the symbol
            let region = state.curr_region();
            let symbol = Self(name);
            region
                .deref_mut(&mut ctx.regions)
                .register_symbol(symbol.clone(), op);
            // construct and return.
            Ok(symbol)
        } else {
            parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![token_wildcard!("@...")].into(), token.kind)
            )
            .into()
        }
    }
}

impl Print for Symbol {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "@{}", self.0)?;
        Ok(())
    }
}

impl From<String> for Symbol {
    fn from(s: String) -> Self {
        if let Some(s) = s.strip_prefix('@') {
            Self(s.to_string())
        } else {
            Self(s)
        }
    }
}

impl From<&str> for Symbol {
    fn from(s: &str) -> Self {
        if let Some(s) = s.strip_prefix('@') {
            Self(s.to_string())
        } else {
            Self(s.to_string())
        }
    }
}

/// A symbol table.
///
/// Symbol table defines the non-SSA values
pub struct SymbolTable {
    /// The symbol name and the operation that defines it.
    symbols: HashMap<String, ArenaPtr<OpObj>>,
    /// The region that the symbol table belongs to.
    region: ArenaPtr<Region>,
}

impl SymbolTable {
    /// Create a new symbol table.
    pub fn new(region: ArenaPtr<Region>) -> Self {
        Self {
            symbols: HashMap::new(),
            region,
        }
    }

    /// Insert a symbol and its definition operation into the table.
    pub fn insert(&mut self, symbol: Symbol, op: ArenaPtr<OpObj>) {
        self.symbols.insert(symbol.0, op);
    }

    /// Get the operation that defines the symbol.
    ///
    /// This might return the operation from the upper-level symbol table.
    pub fn lookup(&self, ctx: &Context, name: &str) -> Option<ArenaPtr<OpObj>> {
        self.symbols.get(name).cloned().or_else(|| {
            self.region
                .deref(&ctx.regions)
                .parent_op()
                .deref(&ctx.ops)
                .as_ref()
                .parent_region(ctx)
                .and_then(|parent_region| {
                    parent_region.deref(&ctx.regions).lookup_symbol(ctx, name)
                })
        })
    }
}

#[derive(Debug, Error)]
pub enum NameAllocDuplicatedErr {
    /// The key is already assigned or allocated with a different name.
    #[error("key is already allocated.")]
    Key,

    /// The name is already assigned or allocated for a different key.
    #[error("name is already allocated.")]
    Name,

    /// The key and name are both duplicated with different values.
    #[error("key and name are both duplicated.")]
    Both,
}

pub struct NameManager<T> {
    counter: u32,
    names: BiMap<ArenaPtr<T>, String>,
}

impl<T> Default for NameManager<T> {
    fn default() -> Self {
        Self {
            counter: 0,
            names: BiMap::default(),
        }
    }
}

impl<T> NameManager<T> {
    pub(super) fn set(
        &mut self,
        ptr: ArenaPtr<T>,
        name: String,
    ) -> Result<(), NameAllocDuplicatedErr> {
        let result = self.names.checked_insert(ptr, name);
        match result {
            Ok(_) => Ok(()),
            Err(Duplicated::Fwd(_)) => Err(NameAllocDuplicatedErr::Key),
            Err(Duplicated::Rev(_)) => Err(NameAllocDuplicatedErr::Name),
            Err(Duplicated::Both(_, _)) => Err(NameAllocDuplicatedErr::Both),
            Err(Duplicated::Full) => Ok(()),
        }
    }

    pub(super) fn get(&mut self, ptr: ArenaPtr<T>) -> String {
        if let Some(name) = self.names.get_fwd(&ptr) {
            return name.clone();
        }

        loop {
            let name = format!("{}", self.counter);
            self.counter += 1;
            if !self.names.contains_rev(&name) {
                self.names.insert(ptr, name.clone());
                return name;
            }
        }
    }

    pub(super) fn get_by_name(&self, name: &str) -> Option<ArenaPtr<T>> {
        self.names.get_rev(&name.to_string()).cloned()
    }
}

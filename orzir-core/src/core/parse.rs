//! The parser for the IR program.
//!
//! OrzIR is similar to MLIR, which is completely extensible, which requires a
//! modular parser to parse the IR program. But different from the MLIR, here we
//! use a simple tokenizer and only support a closed-set of tokens.

use std::{
    cmp,
    fmt::{self, Write},
    io::{Cursor, Read},
};

use thiserror::Error;

use super::context::Context;
use crate::{
    parse_error, support::error::ParseResult, ArenaPtr, Block, OpObj, Print, PrintResult,
    PrintState, Region, RegionKind,
};

/// The position in the source code.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Pos {
    /// The line number.
    line: u32,
    /// The column number.
    column: u32,
    /// The byte offset.
    ///
    /// This will be used to rollback the reader.
    offset: u64,
}

impl fmt::Display for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.column)
    }
}

impl fmt::Debug for Pos {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self) }
}

impl PartialOrd for Pos {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.offset.cmp(&other.offset))
    }
}

impl Ord for Pos {
    fn cmp(&self, other: &Self) -> cmp::Ordering { self.offset.cmp(&other.offset) }
}

impl Pos {
    pub(self) fn new() -> Self {
        Self {
            line: 1,
            column: 0,
            offset: 0,
        }
    }

    /// Update the position with a character.
    pub(self) fn update(&mut self, c: char) {
        if c == '\n' {
            self.line += 1;
            self.column = 0;
        } else {
            self.column += 1;
        }
        self.offset += c.len_utf8() as u64;
    }
}

/// The span of a token/item in the source code.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Span {
    /// The start position.
    pub start: Pos,
    /// The end position.
    pub end: Pos,
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}-{}", self.start, self.end)
    }
}

impl fmt::Debug for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self) }
}

impl Span {
    pub fn new(start: Pos, end: Pos) -> Self { Self { start, end } }

    pub fn merge(&self, other: &Self) -> Self {
        Self {
            start: cmp::min(self.start, other.start),
            end: cmp::max(self.end, other.end),
        }
    }
}

/// A token kind.
#[derive(Clone, PartialEq, Eq)]
pub enum TokenKind {
    /// A character
    ///
    /// For delimiters, only `:`, `=`, `,`, `;`, `*` and `-` are supported. And
    /// for brackets, only `(`, `)`, `{`, `}`, `[`, `]`, `<`, `>` are supported.
    /// `^`, `%`, `!`, `@` will be used for block label, value name, type alias
    /// and symbol name respectively if they are not followed by an identifier,
    /// otherwise they will be treated as normal characters.
    Char(char),
    /// `->`
    Arrow,
    /// A block label starting with `^`.
    BlockLabel(String),
    /// A block name starting with `%`.
    ValueName(String),
    /// A type alias starting with `!`.
    ///
    /// This is the same with MLIR, but not used yet.
    TyAlias(String),
    /// A symbol name starting with `@`.
    SymbolName(String),
    /// Other tokenized string.
    ///
    /// This represents contiguous alphanumeric or with `_`, `.` characters. And
    /// if the string is quoted, there can be escape sequences. This may also
    /// represent numbers, but the parsing process is up to the parser.
    Tokenized(String),
    /// End of file.
    Eof,

    /// The wildcard for block label
    AnyBlockLabel,
    /// The wildcard for value name
    AnyValueName,
    /// The wildcard for type alias
    AnyTyAlias,
    /// The wildcard for symbol name
    AnySymbolName,
    /// The wildcard for any tokenized string.
    AnyTokenized,
}

/// Shortcut to get the [TokenKind] for a delimiter.
#[macro_export]
macro_rules! delimiter {
    ("->") => {
        $crate::TokenKind::Arrow
    };
    (':') => {
        $crate::TokenKind::Char(':')
    };
    ('=') => {
        $crate::TokenKind::Char('=')
    };
    ('(') => {
        $crate::TokenKind::Char('(')
    };
    (')') => {
        $crate::TokenKind::Char(')')
    };
    ('{') => {
        $crate::TokenKind::Char('{')
    };
    ('}') => {
        $crate::TokenKind::Char('}')
    };
    ('[') => {
        $crate::TokenKind::Char('[')
    };
    (']') => {
        $crate::TokenKind::Char(']')
    };
    ('<') => {
        $crate::TokenKind::Char('<')
    };
    ('>') => {
        $crate::TokenKind::Char('>')
    };
    (',') => {
        $crate::TokenKind::Char(',')
    };
    (';') => {
        $crate::TokenKind::Char(';')
    };
    ('*') => {
        $crate::TokenKind::Char('*')
    };
    ('-') => {
        $crate::TokenKind::Char('-')
    };
    ('^') => {
        $crate::TokenKind::Char('^')
    };
    ('%') => {
        $crate::TokenKind::Char('%')
    };
    ('!') => {
        $crate::TokenKind::Char('!')
    };
    ('@') => {
        $crate::TokenKind::Char('@')
    };
}

/// Shortcut to get the [TokenKind] for a wildcard identifier.
#[macro_export]
macro_rules! token_wildcard {
    // char
    ("...") => {
        $crate::TokenKind::AnyTokenized
    };
    ("^...") => {
        $crate::TokenKind::AnyBlockLabel
    };
    ("%...") => {
        $crate::TokenKind::AnyValueName
    };
    ("!...") => {
        $crate::TokenKind::AnyTyAlias
    };
    ("@...") => {
        $crate::TokenKind::AnySymbolName
    };
}

impl TokenKind {
    /// Check if this token kind is compatible with the other.
    pub fn is_compatible(&self, other: &Self) -> bool {
        match (self, other) {
            (TokenKind::Char(ch_0), TokenKind::Char(ch_1)) => ch_0 == ch_1,
            (TokenKind::Arrow, TokenKind::Arrow) => true,
            (TokenKind::BlockLabel(s_0), TokenKind::BlockLabel(s_1)) => s_0 == s_1,
            (TokenKind::ValueName(s_0), TokenKind::ValueName(s_1)) => s_0 == s_1,
            (TokenKind::TyAlias(s_0), TokenKind::TyAlias(s_1)) => s_0 == s_1,
            (TokenKind::SymbolName(s_0), TokenKind::SymbolName(s_1)) => s_0 == s_1,
            (TokenKind::Tokenized(s_0), TokenKind::Tokenized(s_1)) => s_0 == s_1,
            (TokenKind::Eof, TokenKind::Eof) => true,
            // wildcard, the rhs can be any.
            (TokenKind::AnyBlockLabel, TokenKind::BlockLabel(_)) => true,
            (TokenKind::AnyValueName, TokenKind::ValueName(_)) => true,
            (TokenKind::AnyTyAlias, TokenKind::TyAlias(_)) => true,
            (TokenKind::AnySymbolName, TokenKind::SymbolName(_)) => true,
            (TokenKind::AnyTokenized, TokenKind::Tokenized(_)) => true,
            _ => false,
        }
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Char(c) => write!(f, "`{}`", c),
            TokenKind::Arrow => write!(f, "`->`"),
            TokenKind::BlockLabel(s) => write!(f, "`^{}`", s),
            TokenKind::ValueName(s) => write!(f, "`%{}`", s),
            TokenKind::TyAlias(s) => write!(f, "`!{}`", s),
            TokenKind::SymbolName(s) => write!(f, "`@{}`", s),
            TokenKind::Tokenized(s) => write!(f, "`{}`", s),
            TokenKind::Eof => write!(f, "EOF"),
            TokenKind::AnyBlockLabel => write!(f, "`^...`"),
            TokenKind::AnyValueName => write!(f, "`%...`"),
            TokenKind::AnyTyAlias => write!(f, "`!...`"),
            TokenKind::AnySymbolName => write!(f, "`@...`"),
            TokenKind::AnyTokenized => write!(f, "`...`"),
        }
    }
}

impl fmt::Debug for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self) }
}

/// A spanned token.
pub struct Token {
    /// The kind of the token.
    pub kind: TokenKind,
    /// The span of the token.
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self { Self { kind, span } }

    pub fn is_eof(&self) -> bool { matches!(self.kind, TokenKind::Eof) }

    pub fn unwrap_block_label(&self) -> String {
        if let TokenKind::BlockLabel(s) = &self.kind {
            s.clone()
        } else {
            panic!("not a block label");
        }
    }

    pub fn unwrap_value_name(&self) -> String {
        if let TokenKind::ValueName(s) = &self.kind {
            s.clone()
        } else {
            panic!("not a value name");
        }
    }

    pub fn unwrap_ty_alias(&self) -> String {
        if let TokenKind::TyAlias(s) = &self.kind {
            s.clone()
        } else {
            panic!("not a type alias");
        }
    }

    pub fn unwrap_symbol_name(&self) -> String {
        if let TokenKind::SymbolName(s) = &self.kind {
            s.clone()
        } else {
            panic!("not a symbol name");
        }
    }

    pub fn unwrap_tokenized(&self) -> String {
        if let TokenKind::Tokenized(s) = &self.kind {
            s.clone()
        } else {
            panic!("not a tokenized string");
        }
    }
}

/// A tokenizer for the IR program.
///
/// This is used for the [Parse] trait to parse the IR program.
pub struct TokenStream<'a> {
    /// The reader to populate the characters.
    reader: Cursor<&'a str>,
    /// The buffered character for peeking.
    buffered_char: Option<char>,
    /// The buffered token for peeking.
    buffered_token: Option<Token>,
    /// Current position.
    ///
    /// This will be set to peeked position after consuming the buffered token.
    curr_pos: Pos,
    /// The peeked position.
    peeked_pos: Pos,
    /// Checkpoint stack.
    ///
    /// This is used for backtracking the stream, which is useful if there are
    /// optional components.
    ckpts: Vec<Pos>,
}

#[derive(Debug)]
pub struct ExpectedList<T>(Vec<T>);

impl<T> From<Vec<T>> for ExpectedList<T> {
    fn from(v: Vec<T>) -> Self { Self(v) }
}

impl<T: fmt::Display> fmt::Display for ExpectedList<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for (i, item) in self.0.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "{}", item)?;
        }
        write!(f, "]")?;
        Ok(())
    }
}

#[derive(Debug, Error)]
pub enum ParseErrorKind {
    #[error("unclosed block comment")]
    UnclosedBlockComment,

    #[error("invalid character: expected one of {0}, got {1}")]
    InvalidCharacter(ExpectedList<char>, char),

    #[error("unexpected eof")]
    UnexpectedEof,

    #[error("invalid token: expected one of {0}, got {1}")]
    InvalidToken(ExpectedList<TokenKind>, TokenKind),

    #[error("duplicated value name: {0}")]
    DuplicatedValueName(String),

    #[error("invalid result number: expected {0}, got {1}")]
    InvalidResultNumber(usize, usize),

    #[error("invalid trailing type number: expected {0}, got {1}")]
    InvalidTrailingTypeNumber(usize, usize),
}

impl<'a> TokenStream<'a> {
    pub fn new(slice: &'a str) -> Self {
        Self {
            reader: Cursor::new(slice),
            buffered_char: None,
            buffered_token: None,
            curr_pos: Pos::new(),
            peeked_pos: Pos::new(),
            ckpts: Vec::new(),
        }
    }

    /// Peek the next character.
    ///
    /// This will return the buffered character if exists, otherwise read from
    /// the reader, buffer it and return.
    fn peek_char(&mut self) -> Option<char> {
        if let Some(ch) = self.buffered_char {
            return Some(ch);
        }

        let mut buf = [0; 1];
        let ch = match self.reader.read(&mut buf) {
            Ok(0) => None,
            Ok(_) => Some(buf[0] as char),
            Err(_) => None,
        };

        self.buffered_char = ch;
        ch
    }

    /// Consume the buffered character.
    fn consume_char(&mut self) {
        if let Some(c) = self.buffered_char {
            self.peeked_pos.update(c);
            self.buffered_char = None;
        }
    }

    /// Peek and consume the next character.
    fn next_char(&mut self) -> Option<char> {
        let c = self.peek_char();
        self.consume_char();
        c
    }

    fn skip_line_comment(&mut self) {
        loop {
            match self.next_char() {
                Some('\n') | None => break,
                _ => {}
            }
        }
    }

    fn skip_block_comment(&mut self) -> ParseResult<()> {
        let mut depth = 1;
        let start = self.peeked_pos;
        while depth > 0 {
            match self.next_char() {
                Some('/') => {
                    if let Some('*') = self.next_char() {
                        depth += 1;
                    }
                }
                Some('*') => {
                    if let Some('/') = self.next_char() {
                        depth -= 1;
                    }
                }
                Some(_) => {}
                None => {
                    return parse_error!(
                        Span::new(start, self.peeked_pos),
                        ParseErrorKind::UnclosedBlockComment
                    )
                    .into();
                }
            }
        }
        Ok(())
    }

    fn skip_whitespace(&mut self) -> ParseResult<()> {
        loop {
            match self.peek_char() {
                Some(c) if c.is_whitespace() => {
                    self.consume_char();
                }
                Some('/') => {
                    self.consume_char();
                    match self.peek_char() {
                        Some('/') => {
                            self.consume_char();
                            self.skip_line_comment()
                        }
                        Some('*') => {
                            self.consume_char();
                            self.skip_block_comment()?
                        }
                        Some(c) => {
                            return parse_error!(
                                Span::new(self.peeked_pos, self.peeked_pos),
                                ParseErrorKind::InvalidCharacter(vec!['/', '*'].into(), c)
                            )
                            .into();
                        }
                        None => break,
                    }
                }
                Some(_) => break,
                None => break,
            }
        }
        Ok(())
    }

    fn is_delimiter(c: char) -> bool {
        matches!(
            c,
            ':' | '=' | '(' | ')' | '{' | '}' | '[' | ']' | '<' | '>' | ',' | ';' | '*'
        )
    }

    /// Get and buffer the next token.
    ///
    /// This will get the next token, buffer it and return the reference.
    fn buffer_next(&mut self) -> ParseResult<&Token> {
        self.skip_whitespace()?;
        let start = self.peeked_pos;
        let kind = match self.peek_char() {
            Some('^') => {
                self.consume_char();
                let s = self.handle_identifier()?;
                if s.is_empty() {
                    TokenKind::Char('^')
                } else {
                    TokenKind::BlockLabel(s)
                }
            }
            Some('%') => {
                self.consume_char();
                let s = self.handle_identifier()?;
                if s.is_empty() {
                    TokenKind::Char('%')
                } else {
                    TokenKind::ValueName(s)
                }
            }
            Some('!') => {
                self.consume_char();
                let s = self.handle_identifier()?;
                if s.is_empty() {
                    TokenKind::Char('!')
                } else {
                    TokenKind::TyAlias(s)
                }
            }
            Some('@') => {
                self.consume_char();
                let s = self.handle_identifier()?;
                if s.is_empty() {
                    TokenKind::Char('@')
                } else {
                    TokenKind::SymbolName(s)
                }
            }
            Some('-') => {
                self.consume_char();
                match self.peek_char() {
                    Some('>') => {
                        self.consume_char();
                        TokenKind::Arrow
                    }
                    _ => TokenKind::Char('-'),
                }
            }
            Some(c) if Self::is_delimiter(c) => {
                self.consume_char();
                TokenKind::Char(c)
            }
            Some(_) => TokenKind::Tokenized(self.handle_identifier()?),
            None => TokenKind::Eof,
        };

        let end = self.peeked_pos;
        let token = Token::new(kind, Span::new(start, end));

        if let Some(last) = &self.buffered_token {
            if !last.is_eof() {
                self.buffered_token = Some(token);
            } else {
                // if the last token is eof, we should not buffer the new token
            }
        } else {
            self.buffered_token = Some(token);
        }

        Ok(self.buffered_token.as_ref().unwrap())
    }

    /// Set a checkpoint.
    pub fn checkpoint(&mut self) { self.ckpts.push(self.curr_pos); }

    /// Pop the last checkpoint and commit the changes.
    pub fn commit(&mut self) { self.ckpts.pop(); }

    /// Rollback to the last checkpoint.
    ///
    /// This will also reset the buffered token.
    pub fn rollback(&mut self) {
        self.curr_pos = self.ckpts.pop().unwrap();
        self.peeked_pos = self.curr_pos;
        self.reader.set_position(self.curr_pos.offset);
        self.buffered_char = None;
        self.buffered_token = None;
    }

    /// Peek the next token.
    ///
    /// This will return the buffered token if exists, otherwise buffer the next
    pub fn peek(&mut self) -> ParseResult<&Token> {
        if self.buffered_token.is_none() {
            self.buffer_next()?;
        }
        Ok(self.buffered_token.as_ref().unwrap())
    }

    /// Consume the next token.
    pub fn consume(&mut self) -> ParseResult<Token> {
        if self.buffered_token.is_none() {
            self.buffer_next()?;
        }
        let token = self.buffered_token.take().unwrap();
        self.curr_pos = self.peeked_pos;
        Ok(token)
    }

    pub fn consume_if(&mut self, kind: TokenKind) -> ParseResult<Option<Token>> {
        if self.peek()?.kind == kind {
            Ok(Some(self.consume()?))
        } else {
            Ok(None)
        }
    }

    fn handle_identifier(&mut self) -> ParseResult<String> {
        let mut s = String::new();
        let inside_quote = match self.peek_char() {
            Some('"') => {
                self.consume_char();
                s.push('"');
                true
            }
            _ => false,
        };
        loop {
            match self.peek_char() {
                Some(c) if c.is_alphanumeric() || c == '_' || c == '.' => {
                    s.push(c);
                    self.consume_char();
                }
                Some('"') if inside_quote => {
                    self.consume_char();
                    s.push('"');
                    break;
                }
                Some('\\') if inside_quote => {
                    self.consume_char();
                    match self.next_char() {
                        Some(c) => s.push(c),
                        None => {
                            return parse_error!(
                                Span::new(self.peeked_pos, self.peeked_pos),
                                ParseErrorKind::UnexpectedEof
                            )
                            .into();
                        }
                    }
                }
                Some(c) if c.is_whitespace() && inside_quote => {
                    s.push(c);
                    self.consume_char();
                }
                Some(_) => break,
                None => break,
            }
        }
        if s.is_empty() {
            panic!("empty identifier");
        }
        Ok(s)
    }

    pub fn expect(&mut self, kind: TokenKind) -> ParseResult<()> {
        let token = self.consume()?;
        if kind.is_compatible(&token.kind) {
            Ok(())
        } else {
            parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![kind].into(), token.kind)
            )
            .into()
        }
    }

    pub fn curr_pos(&mut self) -> ParseResult<Pos> {
        self.skip_whitespace()?;
        Ok(self.peeked_pos)
    }
}

/// The parse trait for all the components in IR.
pub trait Parse {
    type Item;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item>;
}

pub type ParseFn<Item> = fn(&mut Context, &mut ParseState) -> ParseResult<Item>;

/// The parse state for the parser.
///
/// This is used to store the current state of the parser, including the stream,
/// the stack of ops, regions, blocks, region info, and result names.
pub struct ParseState<'a> {
    pub stream: TokenStream<'a>,
    /// The stack of ops.
    ops: Vec<ArenaPtr<OpObj>>,
    /// The stack of regions.
    regions: Vec<ArenaPtr<Region>>,
    /// The stack of blocks.
    blocks: Vec<ArenaPtr<Block>>,
    /// The stack of region kinds and indices.
    region_info: Vec<(RegionKind, usize)>,
    /// The stack of result names.
    result_names: Vec<Vec<Token>>,
}

impl<'a> ParseState<'a> {
    pub fn new(stream: TokenStream<'a>) -> Self {
        Self {
            stream,
            ops: Vec::new(),
            regions: Vec::new(),
            blocks: Vec::new(),
            region_info: Vec::new(),
            result_names: Vec::new(),
        }
    }

    /// Enter a new op from the current block.
    pub fn enter_op_from(&mut self, block: ArenaPtr<Block>) { self.blocks.push(block); }

    /// Exit the current op.
    pub fn exit_op(&mut self) { self.blocks.pop(); }

    /// Enter an arbitrary operation component.
    pub fn enter_component_from(&mut self, op: ArenaPtr<OpObj>) { self.ops.push(op); }

    /// Exit an arbitrary operation component.
    pub fn exit_component(&mut self) { self.ops.pop().unwrap(); }

    /// Enter a new region from the current op, with the region kind and index.
    pub fn enter_region_with(&mut self, kind: RegionKind, index: usize) {
        self.region_info.push((kind, index));
    }

    /// Exit the current region.
    pub fn exit_region(&mut self) { self.region_info.pop().unwrap(); }

    /// Enter a new block from the current region.
    pub fn enter_block_from(&mut self, region: ArenaPtr<Region>) { self.regions.push(region); }

    /// Exit the current block.
    pub fn exit_block(&mut self) { self.regions.pop().unwrap(); }

    /// Get the current op.
    pub fn curr_op(&self) -> ArenaPtr<OpObj> { *self.ops.last().unwrap() }

    /// Get the current region.
    pub fn curr_region(&self) -> ArenaPtr<Region> { *self.regions.last().unwrap() }

    /// Get the current block.
    pub fn curr_block(&self) -> Option<ArenaPtr<Block>> { self.blocks.last().copied() }

    /// Get the current region kind and index.
    pub fn curr_region_info(&self) -> (RegionKind, usize) { *self.region_info.last().unwrap() }

    /// Get and pop the current result names.
    pub fn pop_result_names(&mut self) -> Vec<Token> { self.result_names.pop().unwrap() }

    /// Push a new series of result name.
    pub fn push_result_names(&mut self, names: Vec<Token>) { self.result_names.push(names); }
}

impl<T: Parse> Parse for Option<T> {
    type Item = Option<T::Item>;

    /// Parsing an optional item.
    ///
    /// This will first try to parse the item, and if failed, rollback the
    /// stream.
    fn parse(ctx: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        state.stream.checkpoint();
        match T::parse(ctx, state) {
            Ok(item) => {
                state.stream.commit();
                Ok(Some(item))
            }
            Err(_) => {
                state.stream.rollback();
                Ok(None)
            }
        }
    }
}

impl Parse for usize {
    type Item = usize;

    fn parse(_: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::Tokenized(s) = token.kind {
            let value = s
                .parse::<usize>()
                .map_err(|e| parse_error!(token.span, e))?;
            Ok(value)
        } else {
            parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![token_wildcard!("...")].into(), token.kind)
            )
            .into()
        }
    }
}

impl Print for usize {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "{}", self)?;
        Ok(())
    }
}

impl Parse for f32 {
    type Item = f32;

    fn parse(_: &mut Context, state: &mut ParseState) -> ParseResult<Self::Item> {
        let token = state.stream.consume()?;
        if let TokenKind::Tokenized(s) = token.kind {
            let value = s.parse::<f32>().map_err(|e| parse_error!(token.span, e))?;
            Ok(value)
        } else {
            parse_error!(
                token.span,
                ParseErrorKind::InvalidToken(vec![token_wildcard!("...")].into(), token.kind)
            )
            .into()
        }
    }
}

impl Print for f32 {
    fn print(&self, _: &Context, state: &mut PrintState) -> PrintResult<()> {
        write!(state.buffer, "{}", self)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{TokenKind, TokenStream};

    #[test]
    fn test_ckpt() {
        let mut stream = TokenStream::new("aaaa b c");
        let pos0 = stream.peek().unwrap().span.start;
        stream.checkpoint();
        let pos1 = stream.peek().unwrap().span.start;
        assert_eq!(
            stream.consume().unwrap().kind,
            TokenKind::Tokenized("aaaa".into())
        );
        assert_eq!(
            stream.consume().unwrap().kind,
            TokenKind::Tokenized("b".into())
        );
        stream.rollback();
        let pos2 = stream.peek().unwrap().span.start;
        assert_eq!(
            stream.consume().unwrap().kind,
            TokenKind::Tokenized("aaaa".into())
        );

        assert_eq!(pos0, pos1);
        assert_eq!(pos1, pos2);
    }
}

use std::{cmp, collections::VecDeque, fmt};

use anyhow::Result;
use thiserror::Error;

use super::context::Context;
use crate::{ArenaPtr, Block, OpObj, Region, RegionKind};

/// The position in the source code.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Pos {
    line: u32,
    column: u32,
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

impl Default for Pos {
    fn default() -> Self {
        Self {
            line: 1,
            column: 0,
            offset: 0,
        }
    }
}

impl Pos {
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
    pub(self) start: Pos,
    pub(self) end: Pos,
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
    pub(super) fn new(start: Pos, end: Pos) -> Self { Self { start, end } }
}

#[derive(Clone, PartialEq, Eq)]
pub enum TokenKind {
    /// A character
    Char(char),
    /// `->`
    Arrow,
    /// A block label starting with `^`.
    BlockLabel(String),
    /// A block name starting with `%`.
    ValueName(String),
    /// A type alias starting with `!`.
    TyAlias(String),
    /// A symbol name starting with `@`.
    SymbolName(String),
    /// A string literal.
    Quoted(String),
    /// Other tokenized string.
    ///
    /// This represents contiguous alphanumeric or with `_`, `-`, `.`
    /// characters.
    Tokenized(String),
    /// End of file.
    Eof,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Char(c) => write!(f, "{}", c),
            TokenKind::Arrow => write!(f, "->"),
            TokenKind::BlockLabel(s) => write!(f, "^{}", s),
            TokenKind::ValueName(s) => write!(f, "%{}", s),
            TokenKind::TyAlias(s) => write!(f, "!{}", s),
            TokenKind::SymbolName(s) => write!(f, "@{}", s),
            TokenKind::Quoted(s) => write!(f, "Quoted({})", s),
            TokenKind::Tokenized(s) => write!(f, "Tokenized({})", s),
            TokenKind::Eof => write!(f, "EOF"),
        }
    }
}

impl fmt::Debug for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{}", self) }
}

pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self { Self { kind, span } }

    pub fn is_eof(&self) -> bool { matches!(self.kind, TokenKind::Eof) }
}

/// A simple reader.
pub(self) struct SliceReader<'a> {
    _slice: &'a str,
    chars: std::str::Chars<'a>,
}

impl<'a> SliceReader<'a> {
    fn new(slice: &'a str) -> Self {
        SliceReader {
            _slice: slice,
            chars: slice.chars(),
        }
    }
}

impl<'a> SliceReader<'a> {
    fn read_char(&mut self) -> Option<char> { self.chars.next() }
}

/// A tokenizer for the IR program.
///
/// This is used for the [Parse] trait to parse the IR program.
pub struct TokenStream<'a> {
    /// The reader to populate the characters.
    reader: SliceReader<'a>,
    /// The current character.
    ///
    /// The backtracking is only one character.
    buffered_char: Option<char>,
    /// The buffered tokens for backtracking.
    ///
    /// The grammar can be LL(1), but here still support backtracking for
    /// simplicity.
    buffered_tokens: VecDeque<Token>,
    /// Current pos.
    pos: Pos,
    /// If eof is reached.
    eof: bool,
}

#[derive(Debug, Error)]
pub enum BasicParseError {
    #[error("unclosed block comment at {0}")]
    UnclosedBlockComment(Span),

    #[error("invalid escape sequence at {0}")]
    InvalidEscapeSequence(Pos),

    #[error("invalid character at {0}")]
    InvalidCharacter(Pos),
}

impl<'a> TokenStream<'a> {
    pub fn new(slice: &'a str) -> Self {
        Self {
            reader: SliceReader::new(slice),
            buffered_char: None,
            buffered_tokens: VecDeque::new(),
            pos: Pos::default(),
            eof: false,
        }
    }

    /// Peek the next character.
    ///
    /// This will return the buffered character if exists, otherwise read from
    /// the reader, buffer it and return.
    fn peek_char(&mut self) -> Result<Option<char>> {
        if let Some(c) = self.buffered_char {
            return Ok(Some(c));
        }
        let ch = self.reader.read_char();
        self.buffered_char = ch;
        if ch.is_none() {
            self.eof = true;
        }
        Ok(ch)
    }

    /// Consume the buffered character.
    fn consume_char(&mut self) {
        if let Some(c) = self.buffered_char {
            self.pos.update(c);
            self.buffered_char = None;
        }
    }

    /// Peek and consume the next character.
    fn next_char(&mut self) -> Result<Option<char>> {
        let c = self.peek_char()?;
        self.consume_char();
        Ok(c)
    }

    fn skip_line_comment(&mut self) -> Result<()> {
        loop {
            match self.next_char()? {
                Some('\n') | None => break,
                _ => {}
            }
        }
        Ok(())
    }

    fn skip_block_comment(&mut self) -> Result<()> {
        let mut depth = 1;
        let start = self.pos;
        while depth > 0 {
            match self.next_char()? {
                Some('/') => {
                    if let Some('*') = self.next_char()? {
                        depth += 1;
                    }
                }
                Some('*') => {
                    if let Some('/') = self.next_char()? {
                        depth -= 1;
                    }
                }
                Some(_) => {}
                None => {
                    return Err(
                        BasicParseError::UnclosedBlockComment(Span::new(start, self.pos)).into(),
                    );
                }
            }
        }
        Ok(())
    }

    fn skip_whitespace(&mut self) -> Result<()> {
        loop {
            match self.peek_char()? {
                Some(c) if c.is_whitespace() => {
                    self.consume_char();
                }
                Some('/') => {
                    self.consume_char();
                    match self.peek_char()? {
                        Some('/') => {
                            self.consume_char();
                            self.skip_line_comment()?
                        }
                        Some('*') => {
                            self.consume_char();
                            self.skip_block_comment()?
                        }
                        Some(_) => {
                            return Err(BasicParseError::InvalidCharacter(self.pos).into());
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

    /// Get and buffer the next token.
    ///
    /// This will get the next token, buffer it and return the reference.
    fn buffer_next(&mut self) -> Result<&Token> {
        self.skip_whitespace()?;
        let start = self.pos;
        let kind = match self.peek_char()? {
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
            Some('"') => {
                // not consume here, just hand over to handle_identifier
                TokenKind::Quoted(self.handle_identifier()?)
            }
            Some(c)
                if matches!(
                    c,
                    ':' | '=' | '(' | ')' | '{' | '}' | '[' | ']' | '<' | '>' | ',' | ';'
                ) =>
            {
                self.consume_char();
                TokenKind::Char(c)
            }
            Some('-') => {
                self.consume_char();
                match self.peek_char()? {
                    Some('>') => {
                        self.consume_char();
                        TokenKind::Arrow
                    }
                    _ => TokenKind::Char('-'),
                }
            }
            Some(_) => TokenKind::Tokenized(self.handle_identifier()?),
            None => TokenKind::Eof,
        };

        let end = self.pos;
        let token = Token::new(kind, Span::new(start, end));

        if let Some(last) = self.buffered_tokens.back() {
            if !last.is_eof() {
                self.buffered_tokens.push_back(token);
            } else {
                // if the last token is eof, we should not buffer the new token
            }
        } else {
            self.buffered_tokens.push_back(token);
        }

        Ok(self.buffered_tokens.back().unwrap())
    }

    /// Peek the next token.
    ///
    /// This will get the front token from the buffer, if the buffer is empty,
    /// call `peek_next` to get the next token.
    pub fn peek(&mut self) -> Result<&Token> {
        if self.buffered_tokens.is_empty() {
            self.buffer_next()?;
        }
        Ok(self.buffered_tokens.front().unwrap())
    }

    /// Consume the next token.
    pub fn consume(&mut self) -> Result<Token> {
        if self.buffered_tokens.is_empty() {
            self.buffer_next()?;
        }
        Ok(self.buffered_tokens.pop_front().unwrap())
    }

    pub fn consume_if(&mut self, kind: TokenKind) -> Result<Option<Token>> {
        if self.peek()?.kind == kind {
            Ok(Some(self.consume()?))
        } else {
            Ok(None)
        }
    }

    /// Rebuffer the token to the front of the buffer.
    pub fn rebuffer(&mut self, token: Token) { self.buffered_tokens.push_front(token); }

    fn handle_identifier(&mut self) -> Result<String> {
        let mut s = String::new();
        let inside_quote = match self.peek_char()? {
            Some('"') => {
                self.consume_char();
                s.push('"');
                true
            }
            _ => false,
        };
        loop {
            match self.peek_char()? {
                Some(c) if c.is_alphanumeric() || c == '_' || c == '-' || c == '.' => {
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
                    match self.next_char()? {
                        Some(c) => s.push(c),
                        None => {
                            return Err(BasicParseError::InvalidEscapeSequence(self.pos).into());
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

    pub fn expect(&mut self, kind: TokenKind) -> Result<()> {
        let token = self.consume()?;
        if token.kind == kind {
            Ok(())
        } else {
            // Err(BasicParseError::InvalidToken(token.span, kind).into())
            anyhow::bail!("invalid token: `{:?}`, expected `{:?}`", token.kind, kind)
        }
    }
}

pub trait Parse {
    type Arg;
    type Item;

    fn parse(arg: Self::Arg, ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item>;
}

pub type ParseFn<Arg, Item> = fn(Arg, &mut Context, &mut ParseState) -> Result<Item>;

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
}

impl<'a> ParseState<'a> {
    pub fn new(stream: TokenStream<'a>) -> Self {
        Self {
            stream,
            ops: Vec::new(),
            regions: Vec::new(),
            blocks: Vec::new(),
            region_info: Vec::new(),
        }
    }

    pub fn enter_op_from(&mut self, block: ArenaPtr<Block>) { self.blocks.push(block); }

    pub fn exit_op(&mut self) { self.blocks.pop(); }

    pub fn enter_region_from(&mut self, op: ArenaPtr<OpObj>, kind: RegionKind, index: usize) {
        self.ops.push(op);
        self.region_info.push((kind, index));
    }

    pub fn exit_region(&mut self) {
        self.region_info.pop().unwrap();
        self.ops.pop().unwrap();
    }

    pub fn enter_block_from(&mut self, region: ArenaPtr<Region>) { self.regions.push(region); }

    pub fn exit_block(&mut self) { self.regions.pop().unwrap(); }

    pub fn curr_op(&self) -> ArenaPtr<OpObj> { *self.ops.last().unwrap() }

    pub fn curr_region(&self) -> ArenaPtr<Region> { *self.regions.last().unwrap() }

    pub fn curr_block(&self) -> Option<ArenaPtr<Block>> { self.blocks.last().copied() }

    pub fn curr_region_info(&self) -> (RegionKind, usize) { *self.region_info.last().unwrap() }
}

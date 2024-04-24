use thiserror::Error;

use crate::core::parse::Span;

#[derive(Debug, Error)]
#[error("parse error: {error} at {span}")]
pub struct ParseError {
    /// The offset of the error in the input string.
    pub span: Span,
    /// The error
    pub error: Box<dyn std::error::Error>,
}

pub type ParseResult<T> = Result<T, ParseError>;

#[macro_export]
macro_rules! parse_error {
    ($span:expr, $error:expr) => {
        $crate::ParseError {
            span: $span,
            error: Box::new($error),
        }
    };
}

impl<T> From<ParseError> for ParseResult<T> {
    fn from(error: ParseError) -> ParseResult<T> { Err(error) }
}

#[derive(Debug, Error)]
#[error("verification error: {error}")]
pub struct VerifyError {
    pub error: Box<dyn std::error::Error>,
}

impl VerifyError {
    pub fn new(error: impl std::error::Error + 'static) -> Self {
        Self {
            error: Box::new(error),
        }
    }
}

pub type VerifyResult<T> = Result<T, VerifyError>;

#[macro_export]
macro_rules! verify_error {
    ($error:expr) => {
        $crate::VerifyError::new($error)
    };
}

impl<T> From<VerifyError> for VerifyResult<T> {
    fn from(error: VerifyError) -> VerifyResult<T> { Err(error) }
}

#[derive(Debug, Error)]
#[error("print error: {error}")]
pub struct PrintError {
    pub error: Box<dyn std::error::Error>,
}

impl PrintError {
    pub fn new(error: impl std::error::Error + 'static) -> Self {
        Self {
            error: Box::new(error),
        }
    }
}

pub type PrintResult<T> = Result<T, PrintError>;

#[macro_export]
macro_rules! print_error {
    ($error:expr) => {
        $crate::PrintError::new($error)
    };
}

impl From<std::fmt::Error> for PrintError {
    fn from(error: std::fmt::Error) -> PrintError { PrintError::new(error) }
}

impl<T> From<PrintError> for PrintResult<T> {
    fn from(error: PrintError) -> PrintResult<T> { Err(error) }
}

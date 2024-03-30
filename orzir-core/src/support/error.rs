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
pub struct VerificationError {
    pub error: Box<dyn std::error::Error>,
}

impl VerificationError {
    pub fn new(error: impl std::error::Error + 'static) -> Self {
        Self {
            error: Box::new(error),
        }
    }
}

pub type VerificationResult<T> = Result<T, VerificationError>;

#[macro_export]
macro_rules! verification_error {
    ($error:expr) => {
        $crate::VerificationError::new($error)
    };
}

impl<T> From<VerificationError> for VerificationResult<T> {
    fn from(error: VerificationError) -> VerificationResult<T> { Err(error) }
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

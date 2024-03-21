/// The builder trait for the builder pattern.
pub trait Build {
    /// The builder type.
    type Builder;
    /// Create a new builder.
    fn builder() -> Self::Builder;
}

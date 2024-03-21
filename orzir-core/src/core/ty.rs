use std::hash::Hash;

use downcast_rs::{impl_downcast, Downcast};
use intertrait::{cast::CastRef, CastFrom};

use crate::support::storage::{ArenaPtr, GetUniqueArenaHash, UniqueArenaHash};

use super::{context::Context, mnemonic::Mnemonic};

pub trait Type: Downcast + CastFrom + GetUniqueArenaHash {
    /// Get the mnemonic of the type.
    fn mnemonic(&self, ctx: &Context) -> Mnemonic;
    /// Get the mnemonic of the type statically.
    fn mnemonic_static(ctx: &Context) -> Mnemonic
    where
        Self: Sized;
    /// Check if the type is equal to another type.
    fn eq(&self, other: &dyn Type) -> bool;
}

impl_downcast!(Type);

pub struct TypeObj(Box<dyn Type>);

impl GetUniqueArenaHash for TypeObj {
    fn unique_arena_hash(&self) -> UniqueArenaHash {
        self.as_inner().unique_arena_hash()
    }
}

pub trait Typed {
    fn ty(&self, ctx: &Context) -> ArenaPtr<TypeObj>;
}

impl<T> From<T> for TypeObj
where
    T: Type,
{
    fn from(t: T) -> Self {
        TypeObj(Box::new(t))
    }
}

impl TypeObj {
    /// Get the inside trait object.
    pub fn as_inner(&self) -> &dyn Type {
        &*self.0
    }

    /// Check if the type object is a concrete type.
    pub fn is_a<T: Type>(&self) -> bool {
        self.as_inner().is::<T>()
    }

    /// Try to downcast the type object to a concrete type.
    pub fn as_a<T: Type>(&self) -> Option<&T> {
        self.as_inner().downcast_ref()
    }

    /// Check if the type object implements a trait.
    pub fn impls<T: Type + ?Sized>(&self) -> bool {
        self.as_inner().impls::<T>()
    }

    /// Try to cast the type object to another trait.
    pub fn cast<T: Type + ?Sized>(&self) -> Option<&T> {
        self.as_inner().cast()
    }
}

impl PartialEq for TypeObj {
    fn eq(&self, other: &Self) -> bool {
        self.as_inner().eq(other.as_inner())
    }
}

impl Eq for TypeObj {}

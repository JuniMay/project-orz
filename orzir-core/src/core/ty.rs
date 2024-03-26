use anyhow::Result;
use downcast_rs::{impl_downcast, Downcast};

use super::{context::Context, mnemonic::Mnemonic, parse::ParseFn};
use crate::{
    support::{
        cast::CastRef,
        storage::{ArenaPtr, GetUniqueArenaHash, UniqueArenaHash},
    },
    Parse, Print, PrintState, TokenStream,
};

pub trait Type: Downcast + GetUniqueArenaHash + Print {
    /// Get the mnemonic of the type.
    fn mnemonic(&self) -> Mnemonic;
    /// Get the mnemonic of the type statically.
    fn mnemonic_static() -> Mnemonic
    where
        Self: Sized;
    /// Check if the type is equal to another type.
    fn eq(&self, other: &dyn Type) -> bool;

    fn register(ctx: &mut Context, parse_fn: TypeParseFn)
    where
        Self: Sized,
    {
        let mnemonic = Self::mnemonic_static();
        ctx.dialects.get_mut(mnemonic.primary()).unwrap().add_type(mnemonic, parse_fn);
    }
}

impl_downcast!(Type);

pub struct TypeObj(Box<dyn Type>);

impl GetUniqueArenaHash for TypeObj {
    fn unique_arena_hash(&self) -> UniqueArenaHash { self.as_inner().unique_arena_hash() }
}

pub trait Typed {
    fn ty(&self, ctx: &Context) -> ArenaPtr<TypeObj>;
}

impl<T> From<T> for TypeObj
where
    T: Type,
{
    fn from(t: T) -> Self { TypeObj(Box::new(t)) }
}

impl TypeObj {
    /// Get the inside trait object.
    pub fn as_inner(&self) -> &dyn Type { &*self.0 }

    /// Check if the type object is a concrete type.
    pub fn is_a<T: Type>(&self) -> bool { self.as_inner().is::<T>() }

    /// Try to downcast the type object to a concrete type.
    pub fn as_a<T: Type>(&self) -> Option<&T> { self.as_inner().downcast_ref() }

    /// Check if the type object implements a trait.
    pub fn impls<T: ?Sized + 'static>(&self, ctx: &Context) -> bool {
        self.as_inner().impls::<T>(&ctx.casters)
    }

    /// Try to cast the type object to another trait.
    pub fn cast_ref<T: ?Sized + 'static>(&self, ctx: &Context) -> Option<&T> {
        self.as_inner().cast_ref(&ctx.casters)
    }
}

impl PartialEq for TypeObj {
    fn eq(&self, other: &Self) -> bool { self.as_inner().eq(other.as_inner()) }
}

impl Eq for TypeObj {}

impl Parse for TypeObj {
    type Arg = ();
    type Item = ArenaPtr<TypeObj>;

    fn parse(_: (), ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        let mnemonic = Mnemonic::parse((), ctx, stream)?;
        let parse_fn = ctx
            .dialects
            .get(mnemonic.primary())
            .unwrap_or_else(|| panic!("dialect {} not found", mnemonic.primary().as_str()))
            .get_type_parse_fn(&mnemonic)
            .unwrap_or_else(|| {
                panic!(
                    "type {}.{} not found",
                    mnemonic.primary().as_str(),
                    mnemonic.secondary().as_str()
                )
            });
        parse_fn((), ctx, stream)
    }
}

pub type TypeParseFn = ParseFn<(), ArenaPtr<TypeObj>>;

impl Print for TypeObj {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        self.as_inner().mnemonic().print(ctx, state)?;
        self.as_inner().print(ctx, state)?;
        Ok(())
    }
}

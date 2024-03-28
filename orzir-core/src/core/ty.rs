use anyhow::Result;
use downcast_rs::{impl_downcast, Downcast};

use super::{
    context::Context,
    mnemonic::Mnemonic,
    parse::{ParseFn, ParseState},
};
use crate::{
    support::{
        cast::CastRef,
        storage::{ArenaPtr, GetUniqueArenaHash, UniqueArenaHash},
    },
    Parse, Print, PrintState, Verify,
};

pub trait Ty: Downcast + GetUniqueArenaHash + Print + Verify {
    /// Get the mnemonic of the type.
    fn mnemonic(&self) -> Mnemonic;
    /// Get the mnemonic of the type statically.
    fn mnemonic_static() -> Mnemonic
    where
        Self: Sized;
    /// Check if the type is equal to another type.
    fn eq(&self, other: &dyn Ty) -> bool;

    fn register(ctx: &mut Context, parse_fn: TyParseFn)
    where
        Self: Sized;
}

impl_downcast!(Ty);

pub struct TyObj(Box<dyn Ty>);

impl GetUniqueArenaHash for TyObj {
    fn unique_arena_hash(&self) -> UniqueArenaHash { self.as_ref().unique_arena_hash() }
}

pub trait Typed {
    fn ty(&self, ctx: &Context) -> ArenaPtr<TyObj>;
}

impl<T> From<T> for TyObj
where
    T: Ty,
{
    fn from(t: T) -> Self { TyObj(Box::new(t)) }
}

impl AsRef<dyn Ty> for TyObj {
    fn as_ref(&self) -> &dyn Ty { &*self.0 }
}

impl TyObj {
    /// Check if the type object is a concrete type.
    pub fn is_a<T: Ty>(&self) -> bool { self.as_ref().is::<T>() }

    /// Try to downcast the type object to a concrete type.
    pub fn as_a<T: Ty>(&self) -> Option<&T> { self.as_ref().downcast_ref() }

    /// Check if the type object implements a trait.
    pub fn impls<T: ?Sized + 'static>(&self, ctx: &Context) -> bool {
        self.as_ref().impls::<T>(&ctx.casters)
    }

    /// Try to cast the type object to another trait.
    pub fn cast_ref<T: ?Sized + 'static>(&self, ctx: &Context) -> Option<&T> {
        self.as_ref().cast_ref(&ctx.casters)
    }
}

impl PartialEq for TyObj {
    fn eq(&self, other: &Self) -> bool { self.as_ref().eq(other.as_ref()) }
}

impl Eq for TyObj {}

impl Parse for TyObj {
    type Item = ArenaPtr<TyObj>;

    fn parse(ctx: &mut Context, state: &mut ParseState) -> Result<Self::Item> {
        let mnemonic = Mnemonic::parse(ctx, state)?;
        let parse_fn = ctx
            .dialects
            .get(mnemonic.primary())
            .unwrap_or_else(|| panic!("dialect {} not found", mnemonic.primary().as_str()))
            .get_ty_parse_fn(&mnemonic)
            .unwrap_or_else(|| {
                panic!(
                    "type {}.{} not found",
                    mnemonic.primary().as_str(),
                    mnemonic.secondary().as_str()
                )
            });
        parse_fn(ctx, state)
    }
}

pub type TyParseFn = ParseFn<ArenaPtr<TyObj>>;

impl Print for TyObj {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        self.as_ref().mnemonic().print(ctx, state)?;
        self.as_ref().print(ctx, state)?;
        Ok(())
    }
}

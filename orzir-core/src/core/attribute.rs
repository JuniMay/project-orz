use anyhow::Result;
use downcast_rs::{impl_downcast, Downcast};
use intertrait::{cast::CastRef, CastFrom};

use crate::{Parse, Print, PrintState, TokenStream};

use super::{context::Context, mnemonic::Mnemonic};

pub trait Attr: Downcast + CastFrom {
    /// Get the mnemonic of the type.
    fn mnemonic(&self, ctx: &Context) -> Mnemonic;
    /// Get the mnemonic of the type statically.
    fn mnemonic_static(ctx: &Context) -> Mnemonic
    where
        Self: Sized;
    /// Check if the type is equal to another type.
    fn eq(&self, other: &dyn Attr) -> bool;
}

impl_downcast!(Attr);

pub struct AttrObj(Box<dyn Attr>);

impl<T> From<T> for AttrObj
where
    T: Attr,
{
    fn from(t: T) -> Self {
        AttrObj(Box::new(t))
    }
}

impl AttrObj {
    /// Get the inside trait object.
    pub fn as_inner(&self) -> &dyn Attr {
        &*self.0
    }

    /// Check if the type object is a concrete type.
    pub fn is_a<T: Attr>(&self) -> bool {
        self.as_inner().is::<T>()
    }

    /// Try to downcast the type object to a concrete type.
    pub fn as_a<T: Attr>(&self) -> Option<&T> {
        self.as_inner().downcast_ref()
    }

    /// Check if the type object implements a trait.
    pub fn impls<T: Attr + ?Sized>(&self) -> bool {
        self.as_inner().impls::<T>()
    }

    /// Try to cast the type object to another trait.
    pub fn cast<T: Attr + ?Sized>(&self) -> Option<&T> {
        self.as_inner().cast()
    }
}

impl PartialEq for AttrObj {
    fn eq(&self, other: &Self) -> bool {
        self.as_inner().eq(other.as_inner())
    }
}

impl Print for AttrObj {
    fn print(&self, ctx: &Context, state: &mut PrintState) -> Result<()> {
        todo!()
    }
}

impl Parse for AttrObj {
    type Arg = ();
    type Item = AttrObj;

    fn parse(_: Self::Arg, ctx: &mut Context, stream: &mut TokenStream) -> Result<Self::Item> {
        todo!()
    }
}

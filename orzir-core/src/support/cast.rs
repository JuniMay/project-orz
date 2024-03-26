use std::{
    any::{Any, TypeId},
    collections::HashMap,
};

use downcast_rs::Downcast;

/// The caster storage.
///
/// This stores the from concrete type, the `Caster<dyn Target>` type and the
/// caster instances.
#[derive(Default)]
pub struct CasterStorage(HashMap<(TypeId, TypeId), Box<dyn Any>>);

/// A caster for trait-to-trait casting.
///
/// Given a trait object and the `dyn Target` type, first upcast it to `dyn
/// Any`, then get the caster using the concrete type id fetched from the `Any`
/// object, and the type id of the concrete caster `Caster<dyn Target>`. The
/// just get the caster from the storage and do the cast.
///
/// The caster functions can be simply implemented by downcasting the `Any`
/// object to the concrete type and then just let rust do the rest type
/// checking.
///
/// # Example
///
/// A caster can be implemented like this:
///
/// ```rust,ignore
/// let caster = Caster::<dyn Target> {
///     cast_ref: |any| any.downcast_ref::<Concrete>().unwrap() as &dyn Target,
///     cast_mut: |any| any.downcast_mut::<Concrete>().unwrap() as &mut dyn Target,
/// }
/// ```
pub struct Caster<T: ?Sized + 'static> {
    /// Casting from any to the target trait.
    cast_ref: fn(&dyn Any) -> &T,
    /// Casting from any to the target trait mutably.
    cast_mut: fn(&mut dyn Any) -> &mut T,
}

impl CasterStorage {
    /// Register a caster into the storage.
    pub fn register<S: ?Sized + 'static, T: ?Sized + 'static>(&mut self, caster: Caster<T>) {
        let concrete_id = TypeId::of::<S>();
        let caster_id = TypeId::of::<Caster<T>>();
        self.0.insert((concrete_id, caster_id), Box::new(caster));
    }

    fn lookup<T: ?Sized + 'static>(&self, id: TypeId) -> Option<&Caster<T>> {
        let caster_id = TypeId::of::<Caster<T>>();
        dbg!(id);
        dbg!(caster_id);
        self.0.get(&(id, caster_id)).map(|c| c.downcast_ref().unwrap())
    }
}

pub trait CastRef {
    fn impls<T: ?Sized + 'static>(&self, caster_storage: &CasterStorage) -> bool;
    fn cast_ref<T: ?Sized + 'static>(&self, caster_storage: &CasterStorage) -> Option<&T>;
}

pub trait CastMut {
    fn cast_mut<T: ?Sized + 'static>(&mut self, caster_storage: &CasterStorage) -> Option<&mut T>;
}

impl<S: Downcast + ?Sized> CastRef for S {
    fn impls<T: ?Sized + 'static>(&self, caster_storage: &CasterStorage) -> bool {
        let any = self.as_any();
        caster_storage.lookup::<T>(any.type_id()).is_some()
    }

    fn cast_ref<T: ?Sized + 'static>(&self, caster_storage: &CasterStorage) -> Option<&T> {
        let any = self.as_any();
        caster_storage.lookup::<T>(any.type_id()).map(|c| (c.cast_ref)(any))
    }
}

impl<S: Downcast + ?Sized> CastMut for S {
    fn cast_mut<T: ?Sized + 'static>(&mut self, caster_storage: &CasterStorage) -> Option<&mut T> {
        let any = self.as_any_mut();
        caster_storage.lookup::<T>((*any).type_id()).map(|c| (c.cast_mut)(any))
    }
}

#[cfg(test)]
mod tests {
    use std::any::TypeId;

    use downcast_rs::Downcast;

    use super::{Caster, CasterStorage};
    use crate::support::cast::{CastMut, CastRef};

    struct ConcreteStruct {
        value: i32,
    }

    trait TraitFrom: Downcast {
        fn identity(&self) -> i32;
    }

    trait TraitTo {
        fn double(&self) -> i32;
        fn set_value(&mut self, value: i32);
    }

    impl TraitFrom for ConcreteStruct {
        fn identity(&self) -> i32 { self.value }
    }

    impl TraitTo for ConcreteStruct {
        fn double(&self) -> i32 { self.value * 2 }

        fn set_value(&mut self, value: i32) { self.value = value; }
    }

    #[test]
    fn test_0() {
        let mut casters = CasterStorage::default();

        casters.register::<ConcreteStruct, dyn TraitTo>(Caster {
            cast_ref: |any| any.downcast_ref::<ConcreteStruct>().unwrap(), // as &dyn TraitTo,
            cast_mut: |any| any.downcast_mut::<ConcreteStruct>().unwrap(), // as &mut dyn TraitTo,
        });

        dbg!(casters.0.keys());
        dbg!(TypeId::of::<ConcreteStruct>());
        dbg!(TypeId::of::<Caster<dyn TraitTo>>());
        dbg!(TypeId::of::<Box<dyn TraitFrom>>());
        dbg!(TypeId::of::<dyn TraitTo>());

        let mut from_obj: Box<dyn TraitFrom> = Box::new(ConcreteStruct { value: 5 });
        assert_eq!(from_obj.identity(), 5);
        // note the box need to be unwrapped by `as_ref`
        let to = from_obj.as_ref().cast_ref::<dyn TraitTo>(&casters).unwrap();
        assert_eq!(to.double(), 10);

        // note the `as_mut` operation.
        let to = from_obj.as_mut().cast_mut::<dyn TraitTo>(&casters).unwrap();
        to.set_value(114514);

        assert_eq!(to.double(), 229028);
        assert_eq!(from_obj.identity(), 114514);
    }
}

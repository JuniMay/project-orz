use orzir_core::{ArenaPtr, TypeObj};
use orzir_macros::{op, ty};

#[op("builtin.module")]
pub struct ModuleOp;

#[derive(Debug, Hash, PartialEq, Eq)]
#[ty("builtin.int")]
pub struct IntType(usize);

#[derive(Debug, Hash, PartialEq, Eq)]
#[ty("builtin.float")]
pub struct Float;

#[derive(Debug, Hash, PartialEq, Eq)]
#[ty("builtin.double")]
pub struct Double;

#[derive(Debug, Hash, PartialEq, Eq)]
#[ty("builtin.tuple")]
pub struct Tuple {
    elems: Vec<ArenaPtr<TypeObj>>,
}

#[cfg(test)]
mod tests {
    use orzir_core::Context;

    use crate::dialects::builtin::{Double, Float, IntType, Tuple};

    #[test]
    fn test_types() {
        let mut ctx = Context::default();

        let int0 = IntType::get(&mut ctx, 32);
        let int1 = IntType::get(&mut ctx, 64);
        let int2 = IntType::get(&mut ctx, 32);
        let float0 = Float::get(&mut ctx);
        let float1 = Float::get(&mut ctx);

        let double0 = Double::get(&mut ctx);
        let double1 = Double::get(&mut ctx);

        assert_ne!(int0, float0);
        assert_ne!(int0, int1);
        assert_eq!(int0, int2);
        assert_eq!(float0, float1);
        assert_ne!(float0, double0);
        assert_eq!(double0, double1);

        let tuple0 = Tuple::get(&mut ctx, vec![int0, float0]);
        let tuple1 = Tuple::get(&mut ctx, vec![int0, float0]);
        let tuple2 = Tuple::get(&mut ctx, vec![int0, float0, double0]);

        assert_eq!(tuple0, tuple1);
        assert_ne!(tuple0, tuple2);
    }
}

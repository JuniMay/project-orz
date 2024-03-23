use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::{Hash, Hasher},
    marker::PhantomData,
};

use std::collections::hash_map::DefaultHasher;

pub struct ArenaPtr<T> {
    index: usize,
    _marker: PhantomData<T>,
}

impl<T> fmt::Debug for ArenaPtr<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "ArenaPtr({})", self.index)
    }
}

impl<T> PartialEq for ArenaPtr<T> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<T> Eq for ArenaPtr<T> {}

impl<T> Hash for ArenaPtr<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.index.hash(state);
    }
}

impl<T> Default for ArenaPtr<T> {
    fn default() -> Self {
        ArenaPtr {
            index: usize::MAX,
            _marker: PhantomData,
        }
    }
}

impl<T> From<usize> for ArenaPtr<T> {
    fn from(index: usize) -> Self {
        ArenaPtr {
            index,
            _marker: PhantomData,
        }
    }
}

impl<T> Clone for ArenaPtr<T> {
    fn clone(&self) -> Self {
        ArenaPtr {
            index: self.index,
            _marker: PhantomData,
        }
    }
}

impl<T> Copy for ArenaPtr<T> {}

impl<T> ArenaPtr<T> {
    pub fn index(&self) -> usize {
        self.index
    }

    pub fn free(self, arena: &mut impl ArenaBase<T>) {
        arena.free(self);
    }

    pub fn try_deref<'a>(&self, arena: &'a impl ArenaBase<T>) -> Option<&'a T> {
        arena.get(*self)
    }

    pub fn try_deref_mut<'a>(&self, arena: &'a mut impl ArenaBase<T>) -> Option<&'a mut T> {
        arena.get_mut(*self)
    }

    pub fn deref<'a>(&self, arena: &'a impl ArenaBase<T>) -> &'a T {
        self.try_deref(arena).expect("ArenaPtr out of bounds")
    }

    pub fn deref_mut<'a>(&self, arena: &'a mut impl ArenaBase<T>) -> &'a mut T {
        self.try_deref_mut(arena).expect("ArenaPtr out of bounds")
    }
}

pub trait ArenaBase<T> {
    /// Allocate a value in the arena.
    fn alloc(&mut self, val: T) -> ArenaPtr<T>;
    /// Free a value in the arena.
    fn free(&mut self, ptr: ArenaPtr<T>);
    /// Get a value in the arena.
    fn get(&self, ptr: ArenaPtr<T>) -> Option<&T>;
    /// Get a mutable value in the arena.
    fn get_mut(&mut self, ptr: ArenaPtr<T>) -> Option<&mut T>;
}

pub enum ArenaEntry<T> {
    Vacant,
    Reserved,
    Occupied(T),
}

/// A simple arena.
pub struct Arena<T> {
    pool: Vec<ArenaEntry<T>>,
    free: HashSet<usize>,
}

impl<T> Default for Arena<T> {
    fn default() -> Self {
        Arena {
            pool: Vec::new(),
            free: HashSet::new(),
        }
    }
}

impl<T> ArenaBase<T> for Arena<T> {
    fn alloc(&mut self, val: T) -> ArenaPtr<T> {
        if let Some(index) = self.free.iter().next().cloned() {
            self.free.remove(&index);
            if let ArenaEntry::Vacant = self.pool[index] {
                self.pool[index] = ArenaEntry::Occupied(val);
            } else {
                unreachable!("ArenaPtr not vacant");
            }
            ArenaPtr::from(index)
        } else {
            self.pool.push(ArenaEntry::Occupied(val));
            ArenaPtr::from(self.pool.len() - 1)
        }
    }

    fn free(&mut self, ptr: ArenaPtr<T>) {
        self.pool[ptr.index()] = ArenaEntry::Vacant;
        self.free.insert(ptr.index());
    }

    fn get(&self, ptr: ArenaPtr<T>) -> Option<&T> {
        let entry = self.pool.get(ptr.index())?;
        match entry {
            ArenaEntry::Vacant => None,
            ArenaEntry::Reserved => None,
            ArenaEntry::Occupied(val) => Some(val),
        }
    }

    fn get_mut(&mut self, ptr: ArenaPtr<T>) -> Option<&mut T> {
        let entry = self.pool.get_mut(ptr.index())?;
        match entry {
            ArenaEntry::Vacant => None,
            ArenaEntry::Reserved => None,
            ArenaEntry::Occupied(val) => Some(val),
        }
    }
}

impl<T> Arena<T> {
    /// Reserve a slot in the arena.
    pub fn reserve(&mut self) -> ArenaPtr<T> {
        if let Some(index) = self.free.iter().next().cloned() {
            self.free.remove(&index);
            self.pool[index] = ArenaEntry::Reserved;
            ArenaPtr::from(index)
        } else {
            self.pool.push(ArenaEntry::Reserved);
            ArenaPtr::from(self.pool.len() - 1)
        }
    }

    /// Fill a reserved slot in the arena.
    pub fn fill(&mut self, ptr: ArenaPtr<T>, val: T) {
        let entry = self.pool.get_mut(ptr.index()).unwrap();
        if let ArenaEntry::Reserved = entry {
            *entry = ArenaEntry::Occupied(val);
        } else if let ArenaEntry::Occupied(_) = entry {
            panic!("ArenaPtr occupied");
        } else {
            panic!("ArenaPtr not reserved");
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct UniqueArenaHash(u64);

impl UniqueArenaHash {
    pub fn new<T: Hash + 'static + ?Sized>(val: &T) -> Self {
        let mut hasher = DefaultHasher::new();
        val.hash(&mut hasher);
        std::any::TypeId::of::<T>().hash(&mut hasher);
        UniqueArenaHash(hasher.finish())
    }
}

pub trait GetUniqueArenaHash {
    fn unique_arena_hash(&self) -> UniqueArenaHash;
}

impl<T> GetUniqueArenaHash for T
where
    T: Hash + 'static + ?Sized,
{
    fn unique_arena_hash(&self) -> UniqueArenaHash {
        UniqueArenaHash::new(self)
    }
}

pub struct UniqueArena<T>
where
    T: GetUniqueArenaHash + Eq,
{
    arena: Arena<T>,
    unique_map: HashMap<UniqueArenaHash, HashSet<ArenaPtr<T>>>,
}

impl<T> Default for UniqueArena<T>
where
    T: GetUniqueArenaHash + Eq,
{
    fn default() -> Self {
        UniqueArena {
            arena: Arena::default(),
            unique_map: HashMap::new(),
        }
    }
}

impl<T> ArenaBase<T> for UniqueArena<T>
where
    T: GetUniqueArenaHash + Eq,
{
    fn alloc(&mut self, val: T) -> ArenaPtr<T> {
        let unique_hash = val.unique_arena_hash();
        if let Some(ptrs) = self.unique_map.get(&unique_hash) {
            for &ptr in ptrs {
                if &val == self.arena.get(ptr).unwrap() {
                    return ptr;
                }
            }
        }

        let ptr = self.arena.alloc(val);
        self.unique_map
            .entry(unique_hash)
            .or_insert_with(HashSet::default)
            .insert(ptr);
        ptr
    }

    fn free(&mut self, ptr: ArenaPtr<T>) {
        let val = ptr.deref(&self.arena);
        let unique_hash = val.unique_arena_hash();
        if self
            .unique_map
            .entry(unique_hash)
            .or_insert_with(HashSet::default)
            .contains(&ptr)
        {
            self.unique_map.get_mut(&unique_hash).unwrap().remove(&ptr);
        }
        self.arena.free(ptr);
    }

    fn get(&self, ptr: ArenaPtr<T>) -> Option<&T> {
        self.arena.get(ptr)
    }

    fn get_mut(&mut self, ptr: ArenaPtr<T>) -> Option<&mut T> {
        self.arena.get_mut(ptr)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Debug, PartialEq, Eq, Hash)]
    struct Test {
        a: i32,
        b: i32,
    }

    #[test]
    fn test_arena() {
        let mut arena = Arena::default();
        let ptr = arena.alloc(Test { a: 1, b: 2 });
        assert_eq!(arena.get(ptr), Some(&Test { a: 1, b: 2 }));
        assert_eq!(arena.get_mut(ptr), Some(&mut Test { a: 1, b: 2 }));
        assert_eq!(arena.get(ptr), Some(&Test { a: 1, b: 2 }));
        assert_eq!(arena.get_mut(ptr), Some(&mut Test { a: 1, b: 2 }));
        ptr.free(&mut arena);
        assert_eq!(arena.get(ptr), None);
        assert_eq!(arena.get_mut(ptr), None);
    }

    #[test]
    fn test_unique_arena() {
        let mut arena = UniqueArena::default();
        let ptr1 = arena.alloc(Test { a: 1, b: 2 });
        let ptr2 = arena.alloc(Test { a: 1, b: 2 });
        assert_eq!(ptr1, ptr2);
        assert_eq!(arena.get(ptr1), Some(&Test { a: 1, b: 2 }));
        assert_eq!(arena.get_mut(ptr1), Some(&mut Test { a: 1, b: 2 }));
        assert_eq!(arena.get(ptr1), Some(&Test { a: 1, b: 2 }));
        assert_eq!(arena.get_mut(ptr1), Some(&mut Test { a: 1, b: 2 }));
        ptr1.free(&mut arena);
        assert_eq!(arena.get(ptr1), None);
        assert_eq!(arena.get_mut(ptr1), None);
        assert_eq!(arena.get(ptr2), None);
        assert_eq!(arena.get_mut(ptr2), None);
    }
}

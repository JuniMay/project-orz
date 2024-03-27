pub enum HoldEntry<T> {
    Vacant,
    Occupied(T),
}

pub struct HoldVec<T> {
    entries: Vec<HoldEntry<T>>,
}

impl<T> HoldVec<T> {
    pub fn new() -> Self {
        Self {
            entries: Vec::new(),
        }
    }

    pub fn resize(&mut self, new_len: usize) {
        self.entries.resize_with(new_len, || HoldEntry::Vacant);
    }

    pub fn set(&mut self, index: usize, value: T) {
        if index >= self.entries.len() {
            self.resize(index + 1);
        }
        self.entries[index] = HoldEntry::Occupied(value);
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        match self.entries.get(index) {
            Some(HoldEntry::Occupied(value)) => Some(value),
            _ => None,
        }
    }
}

impl<T> Default for HoldVec<T> {
    fn default() -> Self { Self::new() }
}

impl<T> std::ops::Index<usize> for HoldVec<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        match self.entries.get(index) {
            Some(HoldEntry::Occupied(value)) => value,
            _ => panic!("HoldVec index out of bounds"),
        }
    }
}

pub struct Hold<T> {
    entry: HoldEntry<T>,
}

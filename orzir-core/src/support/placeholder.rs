/// An entry in a `HoldVec`.
#[derive(Debug, Clone)]
pub enum HoldEntry<T> {
    Vacant,
    Occupied(T),
}

/// A vector that can hold values at arbitrary indices.
///
/// This is similar to `Vec<Option<T>>` or `HashMap<usize, T>`.
pub struct HoldVec<T> {
    entries: Vec<HoldEntry<T>>,
}

impl<T> HoldVec<T> {
    /// Resize the vector.
    ///
    /// If the new length is greater than the current length, the new elements
    /// are initialized with `HoldEntry::Vacant`.
    pub fn resize(&mut self, new_len: usize) {
        self.entries.resize_with(new_len, || HoldEntry::Vacant);
    }

    /// Set the value at the index.
    ///
    /// If the index is out of bounds, the vector is resized.
    pub fn set(&mut self, index: usize, value: T) -> Option<T> {
        if index >= self.entries.len() {
            self.entries.resize_with(index + 1, || HoldEntry::Vacant);
        }
        match self.entries.get_mut(index) {
            Some(HoldEntry::Occupied(old_value)) => std::mem::replace(old_value, value).into(),
            Some(HoldEntry::Vacant) => {
                self.entries[index] = HoldEntry::Occupied(value);
                None
            }
            _ => unreachable!("HoldVec index out of bounds"),
        }
    }

    /// Get the value at the index.
    ///
    /// If the index is out of bounds, `None` is returned.
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.entries.len() {
            return None;
        }
        match self.entries.get(index) {
            Some(HoldEntry::Occupied(value)) => Some(value),
            _ => None,
        }
    }

    /// Get the value at the index.
    pub fn len(&self) -> usize { self.entries.len() }

    /// Check if the vector is empty.
    pub fn is_empty(&self) -> bool { self.entries.is_empty() }
}

impl<T> Default for HoldVec<T> {
    fn default() -> Self {
        Self {
            entries: Vec::new(),
        }
    }
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

/// A placeholder for a value that may or may not be present.
///
/// This is similar to `Option<T>`, but with a different meaning. When deriving
/// [Op](crate::Op), `Hold` should always be used for the deriving fields.
/// 
/// Option can be easily misunderstood as `valid to be None`, but `Hold` stands
/// for `not yet determined`.
pub struct Hold<T> {
    entry: HoldEntry<T>,
}

impl<T> Default for Hold<T> {
    fn default() -> Self {
        Self {
            entry: HoldEntry::Vacant,
        }
    }
}

impl<T> Hold<T> {
    pub fn as_ref(&self) -> Option<&T> {
        match &self.entry {
            HoldEntry::Occupied(value) => Some(value),
            _ => None,
        }
    }
}

impl<T> Hold<T>
where
    T: Copy,
{
    pub fn copied(&self) -> Option<T> {
        match &self.entry {
            HoldEntry::Occupied(value) => Some(*value),
            _ => None,
        }
    }
}

impl<T> Hold<T>
where
    T: Clone,
{
    pub fn cloned(&self) -> Option<T> {
        match &self.entry {
            HoldEntry::Occupied(value) => Some(value.clone()),
            _ => None,
        }
    }
}

impl<T> From<Option<T>> for Hold<T> {
    fn from(o: Option<T>) -> Self {
        match o {
            Some(value) => Self {
                entry: HoldEntry::Occupied(value),
            },
            None => Self {
                entry: HoldEntry::Vacant,
            },
        }
    }
}

impl<T> From<Hold<T>> for Option<T> {
    fn from(h: Hold<T>) -> Self {
        match h.entry {
            HoldEntry::Occupied(value) => Some(value),
            _ => None,
        }
    }
}

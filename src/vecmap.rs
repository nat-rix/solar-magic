use core::cmp::Ord;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VecMap<K, V> {
    items: Vec<(K, V)>,
}

impl<K, V> VecMap<K, V> {
    pub const fn new() -> Self {
        Self { items: vec![] }
    }

    pub fn iter(&self) -> impl Iterator<Item = (&K, &V)> {
        self.items.iter().map(|(k, v)| (k, v))
    }

    pub fn keys(&self) -> impl Iterator<Item = &K> {
        self.items.iter().map(|(k, _)| k)
    }
}

impl<K: Ord, V> VecMap<K, V> {
    pub fn insert(&mut self, k: K, v: V) {
        match self.items.binary_search_by_key(&&k, |(k2, _)| k2) {
            Ok(index) => self.items[index] = (k, v),
            Err(index) => self.items.insert(index, (k, v)),
        }
    }

    pub fn get(&self, k: &K) -> Option<&V> {
        self.items
            .binary_search_by_key(&k, |(k2, _)| k2)
            .ok()
            .and_then(|i| self.items.get(i))
            .map(|(_, v)| v)
    }

    pub fn contains_key(&self, k: &K) -> bool {
        self.get(k).is_some()
    }

    pub fn remove(&mut self, k: &K) -> Option<V> {
        self.items
            .binary_search_by_key(&k, |(k2, _)| k2)
            .ok()
            .map(|index| self.items.remove(index).1)
    }

    pub fn retain(&mut self, mut f: impl FnMut(&K, &mut V) -> bool) {
        self.items.retain_mut(|(k, v)| f(k, v));
    }
}

impl<K, V> Default for VecMap<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

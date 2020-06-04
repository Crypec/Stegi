use std::cmp::Eq;
use std::collections::HashMap;
use std::hash::Hash;

#[derive(Debug)]
pub struct Cxt<K: Eq + Hash + Clone, V: Clone>(Vec<HashMap<K, V>>);

impl<K: Eq + Hash + Clone, V: Clone> Cxt<K, V> {
    pub fn new() -> Self {
        let mut v = Vec::new();
        v.push(HashMap::new());
        Self(v)
    }

    pub fn make(&mut self) {
        let env: HashMap<K, V> = match self.0.last() {
            Some(env) => env.clone(),
            None => HashMap::new(),
        };
        self.0.push(env)
    }

    pub fn drop(&mut self) {
        self.0.pop();
    }

    pub fn insert(&mut self, key: K, val: V) {
        match self.0.last_mut() {
            Some(c) => {
                c.insert(key, val);
            }
            None => {
                self.make();
                self.insert(key, val);
            }
        };
    }

    pub fn get<'a>(&'a mut self, key: &'a K) -> Option<&'a mut V> {
        self.0.last_mut().unwrap().get_mut(&key)
    }
}

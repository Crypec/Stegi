use std::cmp::Eq;
use std::collections::HashMap;
use std::hash::Hash;

#[derive(Debug)]
pub struct Cxt<K: Eq + Hash + Clone, V: Clone> {
    global: HashMap<K, V>,
    stack: Vec<HashMap<K, V>>,
}

impl<K: Eq + Hash + Clone, V: Clone> Cxt<K, V> {
    pub fn new() -> Self {
        Self {
            global: HashMap::new(),
            stack: Vec::new(),
        }
    }

    pub fn make(&mut self) {
        let env: HashMap<K, V> = match self.stack.last() {
            Some(env) => env.clone(),
            None => HashMap::new(),
        };
        self.stack.push(env)
    }

    pub fn make_clean(&mut self) {
        self.stack.push(HashMap::new());
    }

    pub fn drop(&mut self) {
        self.stack.pop();
    }

    pub fn insert(&mut self, key: K, val: V) {
        match self.stack.last_mut() {
            Some(c) => {
                c.insert(key, val);
            }
            None => {
                self.make();
                self.insert(key, val);
            }
        };
    }

    pub fn insert_global(&mut self, k: K, v: V) {
        self.global.insert(k, v);
    }

    pub fn get<'a>(&'a self, k: &'a K) -> Option<V> {
        let val = self.stack.last().unwrap().get(&k);
        match val {
            Some(_) => val.cloned(),
            None => self.global.get(&k).cloned(),
        }
    }

    pub fn get_mut<'a>(&'a mut self, k: &'a K) -> Option<&'a mut V> {
        for frame in self.stack.iter_mut().rev() {
            if frame.contains_key(k) {
                return frame.get_mut(k);
            }
        }
        None
    }
}

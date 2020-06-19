use std::cmp::Eq;
use std::collections::HashMap;
use std::fmt::Debug;
use std::hash::Hash;

type Scope<K, V> = HashMap<K, V>;

type Frame<K, V> = Vec<Scope<K, V>>;

#[derive(Debug)]
pub struct Cxt<K: Eq + Hash + Debug, V: Debug> {
    local: Vec<Frame<K, V>>,
    global: Scope<K, V>,
}

impl<K: Eq + Hash + Debug, V: Debug> Cxt<K, V> {
    pub fn new() -> Self {
        Self {
            local: vec![vec![Scope::new()]],
            global: Scope::new(),
        }
    }

    pub fn push_scope(&mut self) {
        self.local.last_mut().unwrap().push(Scope::new())
    }

    pub fn pop_scope(&mut self) {
        self.local.last_mut().unwrap();
    }

    pub fn push_frame(&mut self) {
        self.local.push(vec![Scope::new()])
    }

    pub fn pop_frame(&mut self) {
        self.local.pop();
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let scope = self
            .local
            .last()
            .unwrap()
            .iter()
            .rev()
            .find(|scope| scope.contains_key(&key));
        match scope {
            Some(scope) => scope.get(&key),
            None => self.global.get(&key),
        }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let scope = self
            .local
            .last_mut()
            .unwrap()
            .iter_mut()
            .rev()
            .find(|scope| scope.contains_key(&key));
        match scope {
            Some(scope) => scope.get_mut(&key),
            None => self.global.get_mut(&key),
        }
    }

    pub fn insert(&mut self, key: K, val: V) {
        self.local
            .last_mut()
            .unwrap()
            .last_mut()
            .unwrap()
            .insert(key, val);
    }

    pub fn insert_global(&mut self, key: K, val: V) {
        self.global.insert(key, val);
    }
}

// #[derive(Debug)]
// pub struct Cxt<K: Eq + Hash + Hash, V> {
//     global: HashMap<K, V>,
//     stack: Vec<HashMap<K, V>>,
// }

// impl<K: Eq + Hash + Clone, V> Cxt<K, V> {
//     pub fn new() -> Self {
//         Self {
//             global: HashMap::new(),
//             stack: Vec::new(),
//         }
//     }

//     pub fn make(&mut self) {
//         let env: HashMap<K, V> = match self.stack.last() {
//             Some(env) => env.clone(),
//             None => HashMap::new(),
//         };
//         self.stack.push(env)
//     }

//     pub fn make_clean(&mut self) {
//         self.stack.push(HashMap::new());
//     }

//     pub fn drop(&mut self) {
//         self.stack.pop();
//     }

//     pub fn insert(&mut self, key: K, val: V) {
//         match self.stack.last_mut() {
//             Some(c) => {
//                 c.insert(key, val);
//             }
//             None => {
//                 self.make();
//                 self.insert(key, val);
//             }
//         };
//     }

//     pub fn insert_global(&mut self, k: K, v: V) {
//         self.global.insert(k, v);
//     }

//     pub fn get<'a>(&'a self, k: &'a K) -> Option<V> {
//         let val = self.stack.last().unwrap().get(&k);
//         match val {
//             Some(_) => val.cloned(),
//             None => self.global.get(&k).cloned(),
//         }
//     }

//     pub fn get_mut<'a>(&'a mut self, k: &'a K) -> Option<&'a mut V> {
//         for frame in self.stack.iter_mut().rev() {
//             if frame.contains_key(k) {
//                 return frame.get_mut(k);
//             }
//         }
//         None
//     }
// }

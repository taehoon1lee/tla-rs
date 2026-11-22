//! Port of `util/UniqueString` + `InternTable`: a global string interner whose ids (`tok`) are assigned in order
//! of first interning. TLC orders string values and model values by this id (`UniqueString.compareTo`), so the
//! order in which the front end interns strings is observable (printing order of sets of strings, CHOOSE).

use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

#[derive(Default)]
pub struct Interner {
    map: HashMap<Arc<str>, u32>,
    names: Vec<Arc<str>>,
}

fn table() -> &'static Mutex<Interner> {
    static T: OnceLock<Mutex<Interner>> = OnceLock::new();
    T.get_or_init(|| Mutex::new(Interner::default()))
}

/// `UniqueString.uniqueStringOf(s).tok`
pub fn intern(s: &str) -> u32 {
    let mut t = table().lock().unwrap();
    if let Some(&i) = t.map.get(s) {
        return i;
    }
    let a: Arc<str> = Arc::from(s);
    let id = t.names.len() as u32;
    t.names.push(a.clone());
    t.map.insert(a, id);
    id
}

pub fn name_of(id: u32) -> Arc<str> {
    let t = table().lock().unwrap();
    t.names[id as usize].clone()
}

/// Reset the table (only for unit tests that need deterministic ids).
pub fn clear_for_tests() {
    let mut t = table().lock().unwrap();
    t.map.clear();
    t.names.clear();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ids_follow_first_interning() {
        let a = intern("zz_first");
        let b = intern("aa_second");
        assert!(a < b);
        assert_eq!(intern("zz_first"), a);
        assert_eq!(&*name_of(b), "aa_second");
    }
}

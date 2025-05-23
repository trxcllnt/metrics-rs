use crate::{atomics::AtomicU64, cow::Cow, IntoLabels, KeyHasher, Label, SharedString};
use std::{
    borrow::Borrow,
    cmp, fmt,
    hash::{Hash, Hasher},
    slice::Iter,
    sync::atomic::{AtomicBool, Ordering},
};

const NO_LABELS: [Label; 0] = [];

/// Name component of a key.
#[derive(Clone, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct KeyName(SharedString);

impl KeyName {
    /// Creates a `KeyName` from a static string.
    pub const fn from_const_str(name: &'static str) -> Self {
        KeyName(SharedString::const_str(name))
    }

    /// Gets a reference to the string used for this name.
    pub fn as_str(&self) -> &str {
        &self.0
    }
}

impl<T> From<T> for KeyName
where
    T: Into<SharedString>,
{
    fn from(name: T) -> Self {
        KeyName(name.into())
    }
}

impl Borrow<str> for KeyName {
    fn borrow(&self) -> &str {
        self.0.borrow()
    }
}

/// A metric identifier.
///
/// A key represents both the name and labels of a metric.
///
/// # Safety
/// Clippy will report any usage of `Key` as the key of a map/set as "mutable key type", meaning
/// that it believes that there is interior mutability present which could lead to a key being
/// hashed different over time.  That behavior could lead to unexpected behavior, as standard
/// maps/sets depend on keys having stable hashes over time, related to times when they must be
/// recomputed as the internal storage is resized and items are moved around.
///
/// In this case, the `Hash` implementation of `Key` does _not_ depend on the fields which Clippy
/// considers mutable (the atomics) and so it is actually safe against differing hashes being
/// generated.  We personally allow this Clippy lint in places where we store the key, such as
/// helper types in the `metrics-util` crate, and you may need to do the same if you're using it in
/// such a way as well.
#[derive(Debug)]
pub struct Key {
    name: KeyName,
    labels: Cow<'static, [Label]>,
    hashed: AtomicBool,
    hash: AtomicU64,
}

impl Key {
    /// Creates a [`Key`] from a name.
    pub fn from_name<N>(name: N) -> Self
    where
        N: Into<KeyName>,
    {
        let name = name.into();
        let labels = Cow::from_owned(Vec::new());

        Self::builder(name, labels)
    }

    /// Creates a [`Key`] from a name and set of labels.
    pub fn from_parts<N, L>(name: N, labels: L) -> Self
    where
        N: Into<KeyName>,
        L: IntoLabels,
    {
        let name = name.into();
        let labels = Cow::from_owned(labels.into_labels());

        Self::builder(name, labels)
    }

    /// Creates a [`Key`] from a non-static name and a static set of labels.
    pub fn from_static_labels<N>(name: N, labels: &'static [Label]) -> Self
    where
        N: Into<KeyName>,
    {
        Self {
            name: name.into(),
            labels: Cow::const_slice(labels),
            hashed: AtomicBool::new(false),
            hash: AtomicU64::new(0),
        }
    }

    /// Creates a [`Key`] from a static name.
    ///
    /// This function is `const`, so it can be used in a static context.
    pub const fn from_static_name(name: &'static str) -> Self {
        Self::from_static_parts(name, &NO_LABELS)
    }

    /// Creates a [`Key`] from a static name and static set of labels.
    ///
    /// This function is `const`, so it can be used in a static context.
    pub const fn from_static_parts(name: &'static str, labels: &'static [Label]) -> Self {
        Self {
            name: KeyName::from_const_str(name),
            labels: Cow::const_slice(labels),
            hashed: AtomicBool::new(false),
            hash: AtomicU64::new(0),
        }
    }

    fn builder(name: KeyName, labels: Cow<'static, [Label]>) -> Self {
        let hash = generate_key_hash(&name, &labels);

        Self { name, labels, hashed: AtomicBool::new(true), hash: AtomicU64::new(hash) }
    }

    /// Name of this key.
    pub fn name(&self) -> &str {
        self.name.0.as_ref()
    }

    /// Labels of this key, if they exist.
    pub fn labels(&self) -> Iter<Label> {
        self.labels.iter()
    }

    /// Consumes this [`Key`], returning the name parts and any labels.
    pub fn into_parts(self) -> (KeyName, Vec<Label>) {
        (self.name, self.labels.into_owned())
    }

    /// Clones this [`Key`], and expands the existing set of labels.
    pub fn with_extra_labels(&self, extra_labels: Vec<Label>) -> Self {
        if extra_labels.is_empty() {
            return self.clone();
        }

        let name = self.name.clone();
        let mut labels = self.labels.clone().into_owned();
        labels.extend(extra_labels);

        Self::builder(name, labels.into())
    }

    /// Gets the hash value for this key.
    pub fn get_hash(&self) -> u64 {
        if self.hashed.load(Ordering::Acquire) {
            self.hash.load(Ordering::Acquire)
        } else {
            let hash = generate_key_hash(&self.name, &self.labels);
            self.hash.store(hash, Ordering::Release);
            self.hashed.store(true, Ordering::Release);
            hash
        }
    }
}

fn generate_key_hash(name: &KeyName, labels: &Cow<'static, [Label]>) -> u64 {
    let mut hasher = KeyHasher::default();
    key_hasher_impl(&mut hasher, name, labels);
    hasher.finish()
}

fn key_hasher_impl<H: Hasher>(state: &mut H, name: &KeyName, labels: &Cow<'static, [Label]>) {
    name.0.hash(state);
    labels.len().hash(state);
    match labels.len() {
        0 => {}
        1 => labels[0].hash(state),
        2 => {
            if labels[0] < labels[1] {
                labels[0].hash(state);
                labels[1].hash(state);
            } else {
                labels[1].hash(state);
                labels[0].hash(state);
            }
        }
        n if n < 8 => {
            let mut labels_sort_map: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
            labels_sort_map[..n].sort_by_key(|i| labels[*i as usize].key());
            for i in 0..n {
                labels[labels_sort_map[i] as usize].hash(state)
            }
        }
        n => {
            let mut labels_sort_map: Vec<usize> = (0..n).collect();
            labels_sort_map.sort_by_key(|i| labels[*i].key());
            for i in 0..n {
                labels[labels_sort_map[i]].hash(state)
            }
        }
    }
}

impl Clone for Key {
    fn clone(&self) -> Self {
        Self {
            name: self.name.clone(),
            labels: self.labels.clone(),
            hashed: AtomicBool::new(self.hashed.load(Ordering::Acquire)),
            hash: AtomicU64::new(self.hash.load(Ordering::Acquire)),
        }
    }
}

impl PartialEq for Key {
    fn eq(&self, other: &Self) -> bool {
        if self.name != other.name {
            return false;
        }
        if self.labels.len() != other.labels.len() {
            return false;
        }
        match self.labels.len() {
            0 => true,
            1 => self.labels[0] == other.labels[0],
            2 => {
                if self.labels[0] == other.labels[0] {
                    self.labels[1] == other.labels[1]
                } else if self.labels[0] == other.labels[1] {
                    self.labels[1] == other.labels[0]
                } else {
                    false
                }
            }
            n if n < 8 => {
                let mut labels_sort_map: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
                labels_sort_map[..n].sort_by_key(|i| self.labels[*i as usize].key());
                let mut his_labels_sort_map: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
                his_labels_sort_map[..n].sort_by_key(|i| other.labels[*i as usize].key());
                for i in 0..n {
                    if self.labels[labels_sort_map[i] as usize]
                        != other.labels[his_labels_sort_map[i] as usize]
                    {
                        return false;
                    }
                }
                true
            }
            n => {
                let mut labels_sort_map: Vec<usize> = (0..n).collect();
                labels_sort_map.sort_by_key(|i| self.labels[*i].key());
                let mut his_labels_sort_map: Vec<usize> = (0..n).collect();
                his_labels_sort_map.sort_by_key(|i| other.labels[*i].key());
                for i in 0..n {
                    if self.labels[labels_sort_map[i]] != other.labels[his_labels_sort_map[i]] {
                        return false;
                    }
                }
                true
            }
        }
    }
}

impl Eq for Key {}

impl PartialOrd for Key {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Key {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match (&self.name, self.labels.len()).cmp(&(&other.name, other.labels.len())) {
            cmp::Ordering::Less => return cmp::Ordering::Less,
            cmp::Ordering::Equal => {}
            cmp::Ordering::Greater => return cmp::Ordering::Greater,
        }
        match self.labels.len() {
            0 => cmp::Ordering::Equal,
            1 => self.labels[0].cmp(&other.labels[0]),
            n if n < 8 => {
                let mut labels_sort_map: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
                labels_sort_map[..n].sort_by_key(|i| self.labels[*i as usize].key());
                let mut his_labels_sort_map: [u8; 8] = [0, 1, 2, 3, 4, 5, 6, 7];
                his_labels_sort_map[..n].sort_by_key(|i| other.labels[*i as usize].key());
                for i in 0..n {
                    match self.labels[labels_sort_map[i] as usize]
                        .cmp(&other.labels[his_labels_sort_map[i] as usize])
                    {
                        cmp::Ordering::Less => return cmp::Ordering::Less,
                        cmp::Ordering::Equal => {}
                        cmp::Ordering::Greater => return cmp::Ordering::Greater,
                    }
                }
                cmp::Ordering::Equal
            }
            n => {
                let mut labels_sort_map: Vec<usize> = (0..n).collect();
                labels_sort_map.sort_by_key(|i| self.labels[*i].key());
                let mut his_labels_sort_map: Vec<usize> = (0..n).collect();
                his_labels_sort_map.sort_by_key(|i| other.labels[*i].key());
                for i in 0..n {
                    match self.labels[labels_sort_map[i]].cmp(&other.labels[his_labels_sort_map[i]])
                    {
                        cmp::Ordering::Less => return cmp::Ordering::Less,
                        cmp::Ordering::Equal => {}
                        cmp::Ordering::Greater => return cmp::Ordering::Greater,
                    }
                }
                cmp::Ordering::Equal
            }
        }
    }
}

impl Hash for Key {
    fn hash<H: Hasher>(&self, state: &mut H) {
        key_hasher_impl(state, &self.name, &self.labels);
    }
}

impl fmt::Display for Key {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.labels.is_empty() {
            write!(f, "Key({})", self.name.as_str())
        } else {
            write!(f, "Key({}, [", self.name.as_str())?;
            let mut first = true;
            for label in self.labels.as_ref() {
                if first {
                    write!(f, "{} = {}", label.0, label.1)?;
                    first = false;
                } else {
                    write!(f, ", {} = {}", label.0, label.1)?;
                }
            }
            write!(f, "])")
        }
    }
}

impl<T> From<T> for Key
where
    T: Into<KeyName>,
{
    fn from(name: T) -> Self {
        Self::from_name(name)
    }
}

impl<N, L> From<(N, L)> for Key
where
    N: Into<KeyName>,
    L: IntoLabels,
{
    fn from(parts: (N, L)) -> Self {
        Self::from_parts(parts.0, parts.1)
    }
}

#[cfg(test)]
mod tests {
    use super::Key;
    use crate::{KeyName, Label};
    use std::{cmp, collections::HashMap, ops::Deref, sync::Arc};

    static BORROWED_NAME: &str = "name";
    static FOOBAR_NAME: &str = "foobar";
    static BORROWED_BASIC: Key = Key::from_static_name(BORROWED_NAME);
    static LABELS: [Label; 1] = [Label::from_static_parts("key", "value")];
    static BORROWED_LABELS: Key = Key::from_static_parts(BORROWED_NAME, &LABELS);

    #[test]
    fn test_key_ord_and_partialord() {
        let keys_expected: Vec<Key> =
            vec![Key::from_name("aaaa"), Key::from_name("bbbb"), Key::from_name("cccc")];

        let keys_unsorted: Vec<Key> =
            vec![Key::from_name("bbbb"), Key::from_name("cccc"), Key::from_name("aaaa")];

        let keys = {
            let mut keys = keys_unsorted.clone();
            keys.sort();
            keys
        };
        assert_eq!(keys, keys_expected);

        let keys = {
            let mut keys = keys_unsorted.clone();
            keys.sort_by(|a, b| a.partial_cmp(b).unwrap());
            keys
        };
        assert_eq!(keys, keys_expected);
    }

    #[test]
    fn test_key_ord_total() {
        let mut keys: Vec<_> = (1..16)
            .flat_map(|i| {
                let names: Vec<Label> =
                    (0..i).map(|s| Label::new(format!("{}", s), format!("{}", s))).collect();
                let key1 = Key::from_parts("key", names.clone());

                // test that changing the order doesn't affect the value
                let mut names_alt = names.clone();
                names_alt.rotate_left(1);
                let key2 = Key::from_parts("key", names_alt);
                assert_eq!(key1, key2);

                // check that the first element affects the order
                names_alt = names.clone();
                names_alt[0] = Label::new("x".to_string(), "0".to_string());
                let key3 = Key::from_parts("key", names_alt);
                assert_ne!(key1, key3);

                // check that the last element affects the order
                names_alt = names.clone();
                names_alt[i - 1] = Label::new("x".to_string(), "0".to_string());
                let key4 = Key::from_parts("key", names_alt);
                assert_ne!(key1, key4);

                [key1, key2, key3, key4]
            })
            .collect();
        keys.push(Key::from_parts("key", vec![]));
        keys.sort();
        for i in 0..keys.len() {
            for j in 0..keys.len() {
                // check that the order is a total order
                match (keys[i] == keys[j], keys[i].cmp(&keys[j])) {
                    (true, cmp::Ordering::Equal) => {}
                    (true, cmp::Ordering::Less) => panic!("at {} {} equal keys compared lt", i, j),
                    (true, cmp::Ordering::Greater) => {
                        panic!("at {} {} equal keys compared gt", i, j)
                    }
                    (false, cmp::Ordering::Equal) => {
                        panic!("at {} {} unequal keys compared equal", i, j)
                    }
                    (false, cmp::Ordering::Less) => assert!(i < j),
                    (false, cmp::Ordering::Greater) => assert!(i > j),
                }
            }
        }
    }

    #[test]
    fn test_key_eq_and_hash() {
        let mut keys = HashMap::new();

        let owned_basic: Key = Key::from_name("name");
        assert_eq!(&owned_basic, &BORROWED_BASIC);

        let previous = keys.insert(owned_basic, 42);
        assert!(previous.is_none());

        let previous = keys.get(&BORROWED_BASIC);
        assert_eq!(previous, Some(&42));

        let labels = LABELS.to_vec();
        let owned_labels = Key::from_parts(BORROWED_NAME, labels);
        assert_eq!(&owned_labels, &BORROWED_LABELS);

        let previous = keys.insert(owned_labels, 43);
        assert!(previous.is_none());

        let previous = keys.get(&BORROWED_LABELS);
        assert_eq!(previous, Some(&43));

        let basic: Key = "constant_key".into();
        let cloned_basic = basic.clone();
        assert_eq!(basic, cloned_basic);

        for i in 1..16 {
            let names: Vec<Label> =
                (0..i).map(|s| Label::new(format!("{}", s), format!("{}", s))).collect();
            let key1 = Key::from_parts("key", names.clone());
            let mut names_alt = names.clone();

            // test that changing the order doesn't affect the hash
            names_alt.rotate_left(1);
            let key2 = Key::from_parts("key", names_alt);
            assert_eq!(key1, key2);
            assert_eq!(key1.get_hash(), key2.get_hash());

            // check that the first element affects the hash
            names_alt = names.clone();
            names_alt[0] = Label::new("x".to_string(), "0".to_string());
            let key2 = Key::from_parts("key", names_alt);
            assert_ne!(key1, key2);
            assert_ne!(key1.get_hash(), key2.get_hash());

            // check that the last element affects the hash
            names_alt = names.clone();
            names_alt[i - 1] = Label::new("x".to_string(), "0".to_string());
            let key2 = Key::from_parts("key", names_alt);
            assert_ne!(key1, key2);
            assert_ne!(key1.get_hash(), key2.get_hash());

            // check that it differs from a key with no labels
            let key2 = Key::from_parts("key", vec![]);
            assert_ne!(key1, key2);
            assert_ne!(key1.get_hash(), key2.get_hash());
        }
    }

    #[test]
    fn test_key_data_proper_display() {
        let key1 = Key::from_name("foobar");
        let result1 = key1.to_string();
        assert_eq!(result1, "Key(foobar)");

        let key2 = Key::from_parts(FOOBAR_NAME, vec![Label::new("system", "http")]);
        let result2 = key2.to_string();
        assert_eq!(result2, "Key(foobar, [system = http])");

        let key3 = Key::from_parts(
            FOOBAR_NAME,
            vec![Label::new("system", "http"), Label::new("user", "joe")],
        );
        let result3 = key3.to_string();
        assert_eq!(result3, "Key(foobar, [system = http, user = joe])");

        let key4 = Key::from_parts(
            FOOBAR_NAME,
            vec![
                Label::new("black", "black"),
                Label::new("lives", "lives"),
                Label::new("matter", "matter"),
            ],
        );
        let result4 = key4.to_string();
        assert_eq!(result4, "Key(foobar, [black = black, lives = lives, matter = matter])");
    }

    #[test]
    fn test_key_name_equality() {
        static KEY_NAME: &str = "key_name";

        let borrowed_const = KeyName::from_const_str(KEY_NAME);
        let borrowed_nonconst = KeyName::from(KEY_NAME);
        let owned = KeyName::from(KEY_NAME.to_owned());

        let shared_arc = Arc::from(KEY_NAME);
        let shared = KeyName::from(Arc::clone(&shared_arc));

        assert_eq!(borrowed_const, borrowed_nonconst);
        assert_eq!(borrowed_const.as_str(), borrowed_nonconst.as_str());
        assert_eq!(borrowed_const, owned);
        assert_eq!(borrowed_const.as_str(), owned.as_str());
        assert_eq!(borrowed_const, shared);
        assert_eq!(borrowed_const.as_str(), shared.as_str());
    }

    #[test]
    fn test_shared_key_name_drop_logic() {
        let shared_arc = Arc::from("foo");
        let shared = KeyName::from(Arc::clone(&shared_arc));

        assert_eq!(shared_arc.deref(), shared.as_str());

        assert_eq!(Arc::strong_count(&shared_arc), 2);
        drop(shared);
        assert_eq!(Arc::strong_count(&shared_arc), 1);

        let shared_weak = Arc::downgrade(&shared_arc);
        assert_eq!(Arc::strong_count(&shared_arc), 1);

        let shared = KeyName::from(Arc::clone(&shared_arc));
        assert_eq!(shared_arc.deref(), shared.as_str());
        assert_eq!(Arc::strong_count(&shared_arc), 2);

        drop(shared_arc);
        assert_eq!(shared_weak.strong_count(), 1);

        drop(shared);
        assert_eq!(shared_weak.strong_count(), 0);
    }
}

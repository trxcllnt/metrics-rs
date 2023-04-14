use std::hash::Hasher;

const FNV_OFFSET_BASIS_64: u64 = 0xcbf29ce484222325;
const FNV_PRIME_64: u64 = 0x00000100000001B3;

/// Key-specific hashing algorithm.
///
/// Currently uses FNV1a - <https://datatracker.ietf.org/doc/html/draft-eastlake-fnv-17.html>
///
/// For any use-case within a `metrics`-owned or adjacent crate, where hashing of a key is required,
/// this is the hasher that will be used.
pub type KeyHasher = Fnv1aConstHasher;

pub struct Fnv1aConstHasher(u64);

impl Fnv1aConstHasher {
    pub const fn new() -> Self {
        Self(FNV_OFFSET_BASIS_64)
    }

    pub const fn const_write(self, bytes: &[u8]) -> Fnv1aConstHasher {
        let mut hash = self.0;

        let mut i = 0;
        let len = bytes.len();
        while i < len {
            hash ^= bytes[i] as u64;
            hash = hash.wrapping_mul(FNV_PRIME_64);
            i += 1;
        }

        Fnv1aConstHasher(hash)
    }

    pub const fn const_finish(&self) -> u64 {
        self.0
    }
}

impl Default for Fnv1aConstHasher {
    fn default() -> Self {
        Self::new()
    }
}

impl Hasher for Fnv1aConstHasher {
    fn finish(&self) -> u64 {
        self.const_finish()
    }

    fn write(&mut self, bytes: &[u8]) {
        let mut hash = Fnv1aConstHasher(self.0);
        hash = hash.const_write(bytes);
        self.0 = hash.0;
    }
}

#[derive(Copy, Clone)]
pub struct Fnv1aHasher(u64);

impl Fnv1aHasher {
    pub const fn new() -> Self {
        Self(FNV_OFFSET_BASIS_64)
    }
}

impl Default for Fnv1aHasher {
    fn default() -> Self {
        Self::new()
    }
}

impl Hasher for Fnv1aHasher {
    fn finish(&self) -> u64 {
        self.0
    }

    fn write(&mut self, bytes: &[u8]) {
        let mut i = 0;
        let len = bytes.len();
        while i < len {
            self.0 ^= bytes[i] as u64;
            self.0 = self.0.wrapping_mul(FNV_PRIME_64);
            i += 1;
        }
    }
}

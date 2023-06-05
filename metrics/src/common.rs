use std::hash::Hasher;

use ahash::AHasher;

use crate::cow::Cow;

/// An allocation-optimized string.
///
/// We specify `SharedString` to attempt to get the best of both worlds: flexibility to provide a
/// static or dynamic (owned) string, while retaining the performance benefits of being able to
/// take ownership of owned strings and borrows of completely static strings.
///
/// `SharedString` can be converted to from either `&'static str` or `String`, with a method,
/// `const_str`, from constructing `SharedString` from `&'static str` in a `const` fashion.
pub type SharedString = Cow<'static, str>;

/// Key-specific hashing algorithm.
///
/// Currently uses AHash - <https://github.com/tkaitchuck/aHash>
///
/// For any use-case within a `metrics`-owned or adjacent crate, where hashing of a key is required,
/// this is the hasher that will be used.
#[derive(Default)]
pub struct KeyHasher(AHasher);

impl Hasher for KeyHasher {
    fn finish(&self) -> u64 {
        self.0.finish()
    }

    fn write(&mut self, bytes: &[u8]) {
        self.0.write(bytes)
    }
}

/// Value of a gauge operation.
#[derive(Clone, Debug)]
pub enum GaugeValue {
    /// Sets the value of the gauge to this value.
    Absolute(f64),
    /// Increments the value of the gauge by this much.
    Increment(f64),
    /// Decrements the value of the gauge by this much.
    Decrement(f64),
}

impl GaugeValue {
    /// Updates an input value based on this gauge value.
    pub fn update_value(&self, input: f64) -> f64 {
        match self {
            GaugeValue::Absolute(val) => *val,
            GaugeValue::Increment(val) => input + val,
            GaugeValue::Decrement(val) => input - val,
        }
    }
}

/// An object which can be converted into a `f64` representation.
///
/// This trait provides a mechanism for existing types, which have a natural representation
/// as a 64-bit floating-point number, to be transparently passed in when recording a histogram.
pub trait IntoF64 {
    /// Converts this object to its `f64` representation.
    fn into_f64(self) -> f64;
}

impl IntoF64 for f64 {
    fn into_f64(self) -> f64 {
        self
    }
}

impl IntoF64 for core::time::Duration {
    fn into_f64(self) -> f64 {
        self.as_secs_f64()
    }
}

/// Helper method to allow monomorphization of values passed to the `histogram!` macro.
#[doc(hidden)]
pub fn __into_f64<V: IntoF64>(value: V) -> f64 {
    value.into_f64()
}

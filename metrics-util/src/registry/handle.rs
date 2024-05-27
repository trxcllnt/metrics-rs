use std::sync::Arc;

/// An atomic handle to a value in a registry.
pub trait AtomicHandle {
    /// The handle's inner value type.
    type Inner;

    /// Whether or not the handle is detached from all other copies.
    ///
    /// If a handle is detached, then no other references to the underlying storage exist. This is
    /// not guaranteed to be a permanent state, and so `try_consume` must be used to atomically
    /// consume (or not) the handle if it found to be detached.
    fn is_detached(&self) -> bool;

    /// Attempts to consume the inner value of this handle, returning it if successful.
    ///
    /// If there are other handles pointing to the same underlying storage, then `Err` is returned
    /// with the original handle value.
    fn try_consume(self) -> Result<Self::Inner, Self> where Self: Sized;
}

impl<T> AtomicHandle for Arc<T> {
    type Inner = T;

    fn is_detached(&self) -> bool {
        Arc::strong_count(self) == 1
    }

    fn try_consume(self) -> Result<Self::Inner, Self> {
        Arc::try_unwrap(self)
    }
}

// TODO: Add some static assertions around the size of `WeakInner`/`StrongInner` always having an
// alignment of at least 2 or more so that we have the niche to store our pointer tag.

use std::{
    marker::PhantomData,
    mem::ManuallyDrop,
    sync::{
        atomic::{AtomicPtr, Ordering},
        Arc, Mutex, Weak,
    },
};

use crate::{IntoF64, Key, Level, Metadata};

macro_rules! metric_handle {
    ($name:ident, $desc:literal, $handler_trait_ty:ident, $register_fn:ident) => {
        #[derive(Clone)]
        #[doc = $desc]
        pub struct $name {
            pointer: Pointer<dyn $handler_trait_ty + Send + Sync + 'static>,
            key: $crate::Key,
            metadata: $crate::Metadata<'static>,
        }

        impl $name {
            /// Creates a no-op handle which does nothing.
            ///
            /// Suitable for use in layers where a handle must be returned to satisfy the recorder
            /// API but no actual metric logic is required.
            pub fn noop() -> Self {
                Self {
                    pointer: Pointer::noop(),
                    key: Key::from_static_name(""),
                    metadata: Metadata::new("", Level::INFO, None),
                }
            }

            /// Creates a $name based on an owned handler.
            pub fn owned<T>(owned: T) -> Self
            where
                T: Into<Pointer<dyn $handler_trait_ty + Send + Sync + 'static>>,
            {
                let pointer = owned.into();
                Self {
                    pointer,
                    key: Key::from_static_name(""),
                    metadata: Metadata::new("", Level::INFO, None),
                }
            }

            /// Creates a $name based on a shared handler.
            pub fn shared<T>(key: Key, metadata: Metadata<'static>, ptr: Arc<T>) -> Self
            where
                T: $handler_trait_ty + Send + Sync + 'static,
            {
                let weak = Arc::downgrade(&ptr);
                Self { pointer: Pointer::weak(weak), key, metadata }
            }

            fn with_ref(&self, f: impl FnOnce(&(dyn $handler_trait_ty + Send + Sync + 'static))) {
                let replace = || self.new_handle_pointer();
                self.pointer.with_ref(f, replace);
            }

            fn new_handle_pointer(&self) -> Pointer<dyn $handler_trait_ty + Send + Sync> {
                let new_handle = $crate::with_recorder(|recorder| {
                    recorder.$register_fn(&self.key, &self.metadata)
                });
                new_handle.pointer
            }
        }

        impl From<Arc<dyn $handler_trait_ty + Send + Sync + 'static>>
            for Pointer<dyn $handler_trait_ty + Send + Sync + 'static>
        {
            fn from(strong: Arc<dyn $handler_trait_ty + Send + Sync + 'static>) -> Self {
                Self::strong(strong)
            }
        }

        impl<T> From<T> for Pointer<dyn $handler_trait_ty + Send + Sync + 'static>
        where
            T: $handler_trait_ty + Send + Sync + 'static,
        {
            fn from(value: T) -> Self {
                Self::strong(Arc::new(value))
            }
        }
    };
}

/// A counter handler.
pub trait CounterFn {
    /// Increments the counter by the given amount.
    fn increment(&self, value: u64);

    /// Sets the counter to at least the given amount.
    ///
    /// This is intended to support use cases where multiple callers are attempting to synchronize
    /// this counter with an external counter that they have no control over.  As multiple callers
    /// may read that external counter, and attempt to set it here, there could be reordering issues
    /// where a caller attempts to set an older (smaller) value after the counter has been updated to
    /// the latest (larger) value.
    ///
    /// This method must cope with those cases.  An example of doing so atomically can be found in
    /// `AtomicCounter`.
    fn absolute(&self, value: u64);
}

/// A gauge handler.
pub trait GaugeFn {
    /// Increments the gauge by the given amount.
    fn increment(&self, value: f64);

    /// Decrements the gauge by the given amount.
    fn decrement(&self, value: f64);

    /// Sets the gauge to the given amount.
    fn set(&self, value: f64);
}

/// A histogram handler.
pub trait HistogramFn {
    /// Records a value into the histogram.
    fn record(&self, value: f64);
}

metric_handle!(Counter, "A counter.", CounterFn, register_counter);

impl Counter {
    /// Increments the counter.
    pub fn increment(&self, value: u64) {
        self.with_ref(|c| c.increment(value));
    }

    /// Sets the counter to an absolute value.
    pub fn absolute(&self, value: u64) {
        self.with_ref(|c| c.absolute(value));
    }
}

metric_handle!(Gauge, "A gauge.", GaugeFn, register_gauge);

impl Gauge {
    /// Increments the gauge.
    pub fn increment<T: IntoF64>(&self, value: T) {
        self.with_ref(move |g| g.increment(value.into_f64()));
    }

    /// Decrements the gauge.
    pub fn decrement<T: IntoF64>(&self, value: T) {
        self.with_ref(move |g| g.decrement(value.into_f64()));
    }

    /// Sets the gauge.
    pub fn set<T: IntoF64>(&self, value: T) {
        self.with_ref(move |g| g.set(value.into_f64()));
    }
}

metric_handle!(Histogram, "A histogram.", HistogramFn, register_histogram);

impl Histogram {
    /// Records a value in the histogram.
    pub fn record<T: IntoF64>(&self, value: T) {
        self.with_ref(move |h| h.record(value.into_f64()));
    }
}

impl<T> CounterFn for Arc<T>
where
    T: CounterFn,
{
    fn increment(&self, value: u64) {
        (**self).increment(value)
    }

    fn absolute(&self, value: u64) {
        (**self).absolute(value)
    }
}
impl<T> GaugeFn for Arc<T>
where
    T: GaugeFn,
{
    fn increment(&self, value: f64) {
        (**self).increment(value)
    }

    fn decrement(&self, value: f64) {
        (**self).decrement(value)
    }

    fn set(&self, value: f64) {
        (**self).set(value)
    }
}

impl<T> HistogramFn for Arc<T>
where
    T: HistogramFn,
{
    fn record(&self, value: f64) {
        (**self).record(value);
    }
}

enum PointerKind<T: ?Sized> {
    Strong { ptr: *mut StrongInner<T> },
    Weak { ptr: *mut WeakInner<T> },
}

impl<T: ?Sized> PointerKind<T> {
    fn from_ptr(ptr: *mut ()) -> Self {
        let ptr_addr = ptr as usize;
        if ptr_addr & 1 == 1 {
            Self::Strong { ptr: (ptr_addr & !1) as *mut StrongInner<T> }
        } else {
            Self::Weak { ptr: ptr as *mut WeakInner<T> }
        }
    }
}

/// Atomic smart pointer that supports replacing itself.
///
/// ## Metric handles and expiration
///
/// In metric handles, we have to deal with the potential that a registry expires a metric, which
/// could otherwise leave a handle attached to a metric that is reported nowhere. In order to handle
/// this, we need the ability to be able to reset/update the internal field that holds the smart
/// pointer reference to the inner data, which requires a mechanism for interior mutability given
/// the immutable references by which handles are accessed through.
///
/// ## Existing smart pointer types
///
/// In nearly all cases, the existing `Arc<T>` from the standard library works for atomically
/// sharing immutable access to some piece of wrapped data. It also additionally supports the trick
/// of being able to be transparently coerced to `Arc<dyn Trait>` from `Arc<T>` if `T: Trait`, which
/// we utilize to allow erasing the concrete type so that the handle types themselves are not
/// required to carry any generic type.
///
/// All of this culiminates in a few requirements:
///
/// - we want to be able to allow callers to use `Arc<T>` where possible because it's already
///   commonly used
/// - we need to be able to support dynamically-sized types for the handle's inner smart pointer
/// - we need a way to expose interior mutability without affecting performance in the normal path
///   (metric not expired)
///
/// `Pointer<T>` provides a mechanism to do this that interoperates with `Arc<T>`.
///
/// ## Design
///
/// Internally, `Pointer<T>` simply manages an atomic pointer to `Arc<T>` (or `Weak<T>`, more on
/// that later) through a newtype wrapper. This is important, as it's a key part of the high
/// performance design. Normally, keeping an atomic pointer directly to `Arc<T>`, by converting it
/// to a raw pointer via `Arc::into_raw`, would only be possible if both of these constraints could
/// be met:
///
/// - ability to destructure a "fat" pointer into its constituent data pointer and virtual table
///   pointer
/// - support for 128-bit atomics (for storing the data pointer + virtual table pointer together)
///
/// While support for 128-bit atomics is generally available, it is not current possible on stable
/// Rust to destructure a fat pointer to even be able to atomically store it. We store `Arc<T>`
/// and `Weak<T>`, even when `T` is unsized, in a newtype wrapper that then provides us a concrete
/// type to reference when creating and storing the raw pointer to those allocations.
///
/// We are acheiving this via double indirection -- first the newtype wrapper, and then
/// `Arc<T>`/`Weak<T>` itself -- which isn't optimal, but crucially, we can load the pointer to the
/// wrapper allocation in a lock-free fashion.
///
/// ## Replacement of weak pointers
///
/// Additionally, we support updating weak pointers in order to reattach them to a live strong reference.
///
/// Like the paradigm of `Arc<T>` and `Weak<T>` being "strong" and "weak" references, `Pointer<T>`
/// allows for the same paradigm. However, as mentioned prior, we have to contend with the potential
/// of a registry expiring a metric, which is the equivalent of all strong references dropping.
///
/// In order to deal with this, all dereference calls (through `with_ref`) must pass a closure which
/// can provide a new `Pointer<T>`, which is meant to act as a replacement. If, upon attempting to
/// dereference a weak pointer, we find that all strong references are gone, we'll replace our own
/// internal pointer state with the state of the replacement pointer.
///
/// This allows us to avoid having to require callers to provide interior mutability around
/// `Pointer<T>` itself in order to reattach a metric handle to the current recorder.
pub struct Pointer<T: ?Sized> {
    ptr: AtomicPtr<()>,
    update: Mutex<()>,
    _ty: PhantomData<T>,
}

#[repr(align(2))]
struct StrongInner<T: ?Sized>(Arc<T>);

#[repr(align(2))]
struct WeakInner<T: ?Sized>(Weak<T>);

// A few static assertions to show we're maintaing our minimum required alignment which is necessary
// to ensure we can safely tag our inner pointer to indicate if it's a strong or weak inner.
const _: () = assert!(
    std::mem::align_of::<StrongInner<()>>() >= 2,
    "alignment of StrongInner<T> must always be 2 or greater"
);
const _: () = assert!(
    std::mem::align_of::<StrongInner<dyn CounterFn>>() >= 2,
    "alignment of StrongInner<T> must always be 2 or greater"
);
const _: () = assert!(
    std::mem::align_of::<WeakInner<()>>() >= 2,
    "alignment of WeakInner<T> must always be 2 or greater"
);
const _: () = assert!(
    std::mem::align_of::<WeakInner<dyn CounterFn>>() >= 2,
    "alignment of WeakInner<T> must always be 2 or greater"
);

impl<T: ?Sized> Pointer<T> {
    /// Creates a no-op pointer.
    fn noop() -> Self {
        Self { ptr: AtomicPtr::new(std::ptr::null_mut()), update: Mutex::new(()), _ty: PhantomData }
    }

    /// Creates a strong pointer.
    fn strong(strong: Arc<T>) -> Self {
        let ptr = Box::into_raw(Box::new(StrongInner(strong)));
        let tagged_ptr = (ptr as usize | 1) as *mut ();
        Self { ptr: AtomicPtr::new(tagged_ptr), update: Mutex::new(()), _ty: PhantomData }
    }

    /// Creates a weak pointer.
    fn weak(weak: Weak<T>) -> Self {
        let ptr = Box::into_raw(Box::new(WeakInner(weak)));
        Self { ptr: AtomicPtr::new(ptr as *mut ()), update: Mutex::new(()), _ty: PhantomData }
    }

    /// Runs the given closure `f` with a reference to the inner data.
    ///
    /// If this is a weak pointer, and the data wrapped by the pointer has gone away, the internal
    /// pointer state is updated to point to a new, valid pointer (by calling `replace` to create a
    /// new pointer which is consumed) before again trying to take a reference to the inner data in
    /// order to call `f`. This logic happens in a loop until a reference is
    /// successfully taken.
    ///
    /// If the pointer is a no-op pointer, `f` and `replace` are not called.
    fn with_ref(&self, f: impl FnOnce(&T), replace: impl Fn() -> Self) {
        loop {
            let ptr = self.ptr.load(Ordering::Acquire);
            if ptr.is_null() {
                // We don't run the given closure if the pointer is a no-op.
                return;
            }

            match PointerKind::from_ptr(ptr) {
                PointerKind::Strong { ptr: strong_ptr } => {
                    let strong = unsafe { &*strong_ptr };
                    f(&strong.0);
                    return;
                }
                PointerKind::Weak { ptr: weak_ptr } => {
                    let weak = unsafe { &*weak_ptr };
                    match weak.0.upgrade() {
                        Some(strong) => {
                            f(&strong);
                            return;
                        }
                        None => {
                            // If the upgrade fails, try and take the update lock.
                            //
                            // When we get the lock, re-check again to see if the pointer is still
                            // the same. If so, we now have exclusive access to update the pointer
                            // by creating a replacement pointer via `replace()` and pointing to the
                            // inner state that it has, effectively consuming it.
                            //
                            // We wrap it in `ManuallyDrop` first to avoid triggering the drop logic
                            // after consuming it.
                            let _guard = self.update.lock().unwrap();
                            let current_ptr = self.ptr.load(Ordering::Acquire);
                            if current_ptr == ptr {
                                let new_pointer = ManuallyDrop::new(replace());
                                let new_ptr = new_pointer.ptr.load(Ordering::Acquire);
                                self.ptr.store(new_ptr, Ordering::Release);
                            }
                        }
                    }
                }
            }
        }
    }
}

impl<T: ?Sized> Drop for Pointer<T> {
    fn drop(&mut self) {
        let ptr = self.ptr.load(Ordering::Acquire);
        if !ptr.is_null() {
            match PointerKind::<T>::from_ptr(ptr) {
                PointerKind::Strong { ptr: strong_ptr } => {
                    // SAFETY: If the pointer is non-null, then we know it came directly from
                    // `Box::into_raw`, so it's pointing to an initialized value, it's aligned, etc.
                    let strong = unsafe { Box::from_raw(strong_ptr) };
                    drop(strong);
                }
                PointerKind::Weak { ptr: weak_ptr } => {
                    // SAFETY: If the pointer is non-null, then we know it came directly from
                    // `Box::into_raw`, so it's pointing to an initialized value, it's aligned, etc.
                    let weak = unsafe { Box::from_raw(weak_ptr) };
                    drop(weak);
                }
            }
        }
    }
}

impl<T: ?Sized> Clone for Pointer<T> {
    fn clone(&self) -> Self {
        let ptr = self.ptr.load(Ordering::Acquire);
        if ptr.is_null() {
            return Self::noop();
        }

        match PointerKind::from_ptr(ptr) {
            PointerKind::Strong { ptr: strong_ptr } => {
                // SAFETY: If the pointer is non-null, then we know it came directly from
                // `Box::into_raw`, so it's pointing to an initialized value, it's aligned, etc.
                let strong = unsafe { &*(strong_ptr as *const StrongInner<T>) };
                Self::strong(Arc::clone(&strong.0))
            }
            PointerKind::Weak { ptr: weak_ptr } => {
                // SAFETY: If the pointer is non-null, then we know it came directly from
                // `Box::into_raw`, so it's pointing to an initialized value, it's aligned, etc.
                let weak = unsafe { &*(weak_ptr as *const WeakInner<T>) };
                Self::weak(Weak::clone(&weak.0))
            }
        }
    }
}

impl<T: ?Sized> From<Weak<T>> for Pointer<T> {
    fn from(weak: Weak<T>) -> Self {
        Self::weak(weak)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc, Weak,
    };

    use super::Pointer;

    struct Handle {
        counter: Arc<AtomicUsize>,
    }

    impl Handle {
        fn increment(&self) {
            self.counter.fetch_add(1, Ordering::AcqRel);
        }
    }

    #[test]
    fn pointer_noop() {
        // Ensure that nothing is actually run when the pointer is a no-op.
        let panic_fn = |_: &()| panic!("should not be called");
        let pointer = Pointer::<()>::noop();
        pointer.with_ref(panic_fn, Pointer::noop)
    }

    #[test]
    fn pointer_strong() {
        // Do a basic test of creating a "strong" pointer from `Arc<T>`, including that we are
        // properly pointed to the originally-wrapped value in `Arc<T>` and that the strong/weak
        // counts are correct once `Pointer<T>` is dropped.

        let counter = Arc::new(AtomicUsize::new(0));
        let handle = Arc::new(Handle { counter: Arc::clone(&counter) });
        let pointer_handle = Arc::clone(&handle);

        let pointer = Pointer::strong(pointer_handle);
        assert_eq!(2, Arc::strong_count(&handle));
        assert_eq!(0, Arc::weak_count(&handle));

        assert_eq!(0, counter.load(Ordering::Acquire));
        pointer.with_ref(|h: &Handle| h.increment(), Pointer::noop);
        assert_eq!(1, counter.load(Ordering::Acquire));

        drop(pointer);
        assert_eq!(1, Arc::strong_count(&handle));
        assert_eq!(0, Arc::weak_count(&handle));
    }

    #[test]
    fn pointer_strong_drop() {
        // Do a basic test of creating a "strong" pointer from `Arc<T>` and then dropping
        // `Pointer<T>`, ensuring that the wrapped `Arc<T>` is actually dropped.

        let handle = Arc::new(Handle { counter: Arc::new(AtomicUsize::new(0)) });
        let pointer_handle = Arc::clone(&handle);

        let pointer = Pointer::strong(pointer_handle);

        assert_eq!(2, Arc::strong_count(&handle));
        drop(pointer);
        assert_eq!(1, Arc::strong_count(&handle));
    }

    #[test]
    fn pointer_weak() {
        // Do a basic test of creating a "weak" pointer from `Weak<T>`, including that we are
        // properly pointed to the originally-wrapped value in `Weak<T>` and that the strong/weak
        // counts are correct once `Pointer<T>` is dropped.

        let counter = Arc::new(AtomicUsize::new(0));
        let handle = Arc::new(Handle { counter: Arc::clone(&counter) });
        let pointer_handle = Arc::downgrade(&handle);

        let pointer = Pointer::weak(pointer_handle);
        assert_eq!(1, Arc::strong_count(&handle));
        assert_eq!(1, Arc::weak_count(&handle));

        assert_eq!(0, counter.load(Ordering::Acquire));
        pointer.with_ref(|h: &Handle| h.increment(), Pointer::noop);
        assert_eq!(1, counter.load(Ordering::Acquire));

        drop(pointer);
        assert_eq!(1, Arc::strong_count(&handle));
        assert_eq!(0, Arc::weak_count(&handle));
    }

    #[test]
    fn pointer_weak_drop() {
        // Do a basic test of creating a "weak" pointer from `Weak<T>` and then dropping
        // `Pointer<T>`, ensuring that the wrapped `Weak<T>` is actually dropped.

        let handle = Arc::new(Handle { counter: Arc::new(AtomicUsize::new(0)) });
        let pointer_handle = Arc::downgrade(&handle);

        let pointer = Pointer::weak(pointer_handle);

        assert_eq!(1, Arc::weak_count(&handle));
        drop(pointer);
        assert_eq!(0, Arc::weak_count(&handle));
    }

    #[test]
    fn pointer_weak_replace() {
        // Do a basic test of replacing a "weak" pointer, where a weak pointer to handle #1 is
        // created, and then handle #1 is dropped, which should lead to the existing weak pointer
        // getting reattached to handle #2.

        let counter1 = Arc::new(AtomicUsize::new(0));
        let handle1 = Arc::new(Handle { counter: Arc::clone(&counter1) });
        let pointer_handle1 = Arc::downgrade(&handle1);

        let counter2 = Arc::new(AtomicUsize::new(10));
        let handle2 = Arc::new(Handle { counter: Arc::clone(&counter2) });
        let pointer_handle2 = Arc::downgrade(&handle2);

        let pointer = Pointer::weak(pointer_handle1);
        assert_eq!(1, Arc::strong_count(&handle1));
        assert_eq!(1, Arc::weak_count(&handle1));

        assert_eq!(0, counter1.load(Ordering::Acquire));
        pointer.with_ref(|h: &Handle| h.increment(), Pointer::noop);
        assert_eq!(1, counter1.load(Ordering::Acquire));

        assert_eq!(10, counter2.load(Ordering::Acquire));
        drop(handle1);
        assert_eq!(1, Arc::strong_count(&counter1));

        assert_eq!(1, Arc::strong_count(&handle2));
        assert_eq!(1, Arc::weak_count(&handle2));
        pointer
            .with_ref(|h: &Handle| h.increment(), || Pointer::weak(Weak::clone(&pointer_handle2)));
        assert_eq!(1, counter1.load(Ordering::Acquire));
        assert_eq!(11, counter2.load(Ordering::Acquire));
        assert_eq!(1, Arc::strong_count(&handle2));
        assert_eq!(2, Arc::weak_count(&handle2));
    }
}

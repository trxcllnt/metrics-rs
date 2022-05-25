// TODO: We utilize the capacity field in `Metadata` as the sentinel value for "we-re holding an Arc<T>" but this
// technically depends on the fact that Rust says it will not issue an allocation larger than `isize::MAX`, except maybe
// on 32-bit systems? even then, it would still mean needing to get a string that was 2GB or larger which is just
// like... not going to happen in real-life.
//
// _however_, we should be correct where we can be, so we should add a check to `from_owned` to enforce having a
// capacity that isn't equal to `usize::MAX`. that's enough to ensure that our sentinel value is viable, and tbh, i
// don't care about panicking if some weirdo has a string with enough reserved capacity to allocate usize::MAX bytes on
// their platform. that ain't my problem.

use std::{
    marker::PhantomData,
    mem::ManuallyDrop,
    ops::Deref,
    ptr::{slice_from_raw_parts, NonNull},
    sync::Arc,
};

use crate::Label;

#[derive(Clone, Copy)]
enum Kind {
    Owned,
    Borrowed,
    Shared,
}

/// A clone-on-write smart pointer with an optimized memory layout.
/// 
// TODO: Can we actually do a union of the normal pointer/metadata internals and a straight 24 byte array, used to hold
// a string? Basically a clone of bodil's `smartstring`, since we can entirely avoid an allocation when using owned
// values, preferring to copy them instead.
pub struct Cow2<'a, T: Cow2able + ?Sized + 'a> {
    /// Pointer to data.
    ptr: NonNull<T::Pointer>,

    /// Pointer metadata: length, capacity, and kind.
    metadata: Metadata,

    /// Lifetime marker.
    marker: PhantomData<&'a T>,
}

impl<T> Cow2<'_, T>
where
    T: Cow2able + ?Sized,
{
    pub fn from_owned(owned: T::Owned) -> Self {
        let (ptr, metadata) = T::owned_into_parts(owned);

        if metadata.capacity() == usize::MAX {
            panic!("invalid capacity of usize::MAX for owned value");
        }

        Self { ptr, metadata, marker: PhantomData }
    }

    pub fn from_shared(arc: Arc<T>) -> Self {
        let (ptr, metadata) = T::shared_into_parts(arc);

        Self { ptr, metadata, marker: PhantomData }
    }

    pub fn into_owned(self) -> T::Owned {
        // We have to ensure that the `Drop` impl does _not_ run because we're taking ownership back in the case of
        // holding an owned value. `owned_from_parts` handles any necessary dropping that must occur i.e. if we're holding
        // an `Arc<T>`.
        let cow = ManuallyDrop::new(self);

        T::owned_from_parts(cow.ptr, &cow.metadata)
    }
}

impl<'a, T> Cow2<'a, T>
where
    T: Cow2able + ?Sized,
{
    pub fn from_borrowed(borrowed: &'a T) -> Self {
        let (ptr, metadata) = T::borrowed_into_parts(borrowed);

        Self { ptr, metadata, marker: PhantomData }
    }
}

impl<T> Deref for Cow2<'_, T>
where
    T: Cow2able + ?Sized,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe {
            let ptr = T::borrowed_from_parts(self.ptr, &self.metadata);
            ptr.as_ref().unwrap()
        }
    }
}

impl<T> Clone for Cow2<'_, T>
where
    T: Cow2able + ?Sized,
{
    fn clone(&self) -> Self {
        let (ptr, metadata) = T::clone_from_parts(self.ptr, &self.metadata);

        Self { ptr, metadata, marker: PhantomData }
    }
}

impl<T> Drop for Cow2<'_, T>
where
    T: Cow2able + ?Sized,
{
    fn drop(&mut self) {
        T::drop_from_parts(self.ptr, &self.metadata)
    }
}

// Implementations of constant functions for creating `Cow` via static strings, static string
// slices, and static label slices.
impl<'a> Cow2<'a, str> {
    pub const fn const_str(val: &'a str) -> Self {
        Self {
            // We are casting *const T to *mut T, however for all borrowed values
            // this raw pointer is only ever dereferenced back to &T.
            ptr: unsafe { NonNull::new_unchecked(val.as_ptr() as *mut _) },
            metadata: Metadata::borrowed(val.len()),
            marker: PhantomData,
        }
    }
}

impl<'a> Cow2<'a, [Label]> {
    pub const fn const_slice(val: &'a [Label]) -> Cow2<'a, [Label]> {
        Self {
            ptr: unsafe { NonNull::new_unchecked(val.as_ptr() as *mut _) },
            metadata: Metadata::borrowed(val.len()),
            marker: PhantomData,
        }
    }
}

/*

This will be possible in 1.61.0 when `const_fn_trait_bound` is stabilized.

impl<'a, T> Cow2<'a, [T]>
where
    T: Cow2able + Clone + ?Sized,
{
    pub const fn const_slice(val: &'a [T]) -> Cow2<'a, [T]> {
        Self {
            ptr: unsafe { NonNull::new_unchecked(val.as_ptr() as *mut _) },
            metadata: Metadata::borrowed(val.len()),
            marker: PhantomData,
        }
    }
}

*/

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Metadata(usize, usize);

impl Metadata {
    #[inline]
    fn length(&self) -> usize {
        self.0
    }

    #[inline]
    fn capacity(&self) -> usize {
        self.1
    }

    #[inline]
    fn kind(&self) -> Kind {
        match (self.0, self.1) {
            (_, usize::MAX) => Kind::Shared,
            (_, 0) => Kind::Borrowed,
            _ => Kind::Owned,
        }
    }

    pub const fn arc(length: usize) -> Metadata {
        Metadata(length, usize::MAX)
    }

    pub const fn borrowed(len: usize) -> Metadata {
        Metadata(len, 0)
    }

    pub const fn owned(len: usize, capacity: usize) -> Metadata {
        Metadata(len, capacity)
    }
}

pub trait Cow2able {
    type Pointer;
    type Owned;

    fn borrowed_into_parts(&self) -> (NonNull<Self::Pointer>, Metadata);
    fn owned_into_parts(owned: Self::Owned) -> (NonNull<Self::Pointer>, Metadata);
    fn shared_into_parts(arc: Arc<Self>) -> (NonNull<Self::Pointer>, Metadata);

    fn borrowed_from_parts(ptr: NonNull<Self::Pointer>, metadata: &Metadata) -> *const Self;
    fn owned_from_parts(ptr: NonNull<Self::Pointer>, metadata: &Metadata) -> Self::Owned;
    fn clone_from_parts(
        ptr: NonNull<Self::Pointer>,
        metadata: &Metadata,
    ) -> (NonNull<Self::Pointer>, Metadata);
    fn drop_from_parts(ptr: NonNull<Self::Pointer>, metadata: &Metadata);
}

impl Cow2able for str {
    type Pointer = u8;
    type Owned = String;

    #[inline]
    fn borrowed_into_parts(&self) -> (NonNull<Self::Pointer>, Metadata) {
        let ptr = unsafe { NonNull::new_unchecked(self.as_ptr() as *mut _) };
        let metadata = Metadata::borrowed(self.len());
        (ptr, metadata)
    }

    #[inline]
    fn owned_into_parts(owned: Self::Owned) -> (NonNull<Self::Pointer>, Metadata) {
        let mut owned = ManuallyDrop::new(owned.into_bytes());
        let ptr = unsafe { NonNull::new_unchecked(owned.as_mut_ptr()) };
        let metadata = Metadata::owned(owned.len(), owned.capacity());
        (ptr, metadata)
    }

    #[inline]
    fn shared_into_parts(arc: Arc<Self>) -> (NonNull<Self::Pointer>, Metadata) {
        let metadata = Metadata::arc(arc.len());
        let ptr = unsafe { NonNull::new_unchecked(Arc::into_raw(arc) as *mut _) };
        (ptr, metadata)
    }

    #[inline]
    fn borrowed_from_parts(ptr: NonNull<Self::Pointer>, metadata: &Metadata) -> *const Self {
        slice_from_raw_parts(ptr.as_ptr(), metadata.length()) as *const _
    }

    #[inline]
    fn owned_from_parts(ptr: NonNull<Self::Pointer>, metadata: &Metadata) -> Self::Owned {
        match metadata.kind() {
            // If we have a reference, well, then yeah, we need to clone to `String` via `to_string`. We own nothing so
            // there's nothing to drop.
            Kind::Borrowed => {
                let s = unsafe { &*Self::borrowed_from_parts(ptr, &metadata) };
                s.to_string()
            }
            // We're reconstituting the `String` directly from the backing storage, rather than first reconstituing the
            // `Vec<u8>` and then using the safe methods on `String`, because, well, we already know we got a valid
            // `String` originally.
            Kind::Owned => unsafe {
                String::from_raw_parts(ptr.as_ptr(), metadata.length(), metadata.capacity())
            },
            // We specifically do _not_ forget the `Arc<str>` here, like we do in `clone_from_parts`.
            //
            // This method overall is called when `Cow2` is being consumed.  In the case of `Cow2` owning the string,
            // letting the `Drop` impl run would try to deallocate that string, which obviously wouldn't fly, so we
            // ensure thre `Drop` impl doesn't run... but that doesn't work here, because we're not able to consume
            // anything from `Arc<str>`, so we only need a reference to call `to_string` but we can't leave our
            // `Arc<str>` dangling... so we have to make sure it drops here.
            Kind::Shared => {
                let s = unsafe { Arc::from_raw(Self::borrowed_from_parts(ptr, metadata)) };
                s.to_string()
            }
        }
    }

    #[inline]
    fn clone_from_parts(
        ptr: NonNull<Self::Pointer>,
        metadata: &Metadata,
    ) -> (NonNull<Self::Pointer>, Metadata) {
        match metadata.kind() {
            // As we're operating on a reference, `Cow2` is bound to the lifetime of tthat source reference. In turn, we
            // can safely the same pointer/metadata to that reference for the clone of `Cow2` so long as the lifetimes
            // as identical, as the clone cannot go out-of-scope any later than the original `Cow2` will.
            Kind::Borrowed => (ptr, *metadata),
            // Small deduplication of code by using the same code as we would to get an owned version of a referenced
            // `Cow2`, given that both a referenced and owned version ultimately point to a [u8].
            Kind::Owned => Self::owned_into_parts(Self::owned_from_parts(ptr, metadata)),
            // We have to reconstruct the `Arc` so we can correctly clone it but we _also_ have to make sure that we
            // forget `original` so that we don't drop it early and invalidate the actual string being pointed to.
            Kind::Shared => {
                let original = unsafe { Arc::from_raw(Self::borrowed_from_parts(ptr, metadata)) };
                let new = Arc::clone(&original);

                // SAFETY: The backing `Arc<str>` will be dropped via the `Drop` impl for `Cow2`.
                std::mem::forget(original);
                Self::shared_into_parts(new)
            }
        }
    }

    #[inline]
    fn drop_from_parts(ptr: NonNull<Self::Pointer>, metadata: &Metadata) {
        match metadata.kind() {
            // References don't own anything, so there's nothing to drop.
            Kind::Borrowed => {}
            // We originally took in a `String`, but we decomposed it to its backing `Vec<u8>`, so we can simply
            // reconstruct the `Vec<u8>` without having to go through the process of also recreating the `String`, which
            // would involve revalidating the input bytes as valid UTF-8, and so on.
            Kind::Owned => {
                let owned = unsafe {
                    Vec::from_raw_parts(ptr.as_ptr(), metadata.length(), metadata.capacity())
                };
                drop(owned);
            }
            // We just need to reconstitute the `Arc<str>` so it can run its own drop logic.
            Kind::Shared => {
                let arc = unsafe { Arc::from_raw(Self::borrowed_from_parts(ptr, metadata)) };
                drop(arc);
            }
        }
    }
}

impl<T> Cow2able for [T]
where
    T: Clone,
{
    type Pointer = T;
    type Owned = Vec<T>;

    #[inline]
    fn borrowed_into_parts(&self) -> (NonNull<Self::Pointer>, Metadata) {
        let ptr = unsafe { NonNull::new_unchecked(self.as_ptr() as *mut _) };
        let metadata = Metadata::borrowed(self.len());
        (ptr, metadata)
    }

    #[inline]
    fn owned_into_parts(owned: Self::Owned) -> (NonNull<Self::Pointer>, Metadata) {
        let mut owned = ManuallyDrop::new(owned);
        let ptr = unsafe { NonNull::new_unchecked(owned.as_mut_ptr()) };
        let metadata = Metadata::owned(owned.len(), owned.capacity());
        (ptr, metadata)
    }

    #[inline]
    fn shared_into_parts(arc: Arc<Self>) -> (NonNull<Self::Pointer>, Metadata) {
        let metadata = Metadata::arc(arc.len());
        let ptr = unsafe { NonNull::new_unchecked(Arc::into_raw(arc) as *mut _) };
        (ptr, metadata)
    }

    #[inline]
    fn borrowed_from_parts(ptr: NonNull<Self::Pointer>, metadata: &Metadata) -> *const Self {
        slice_from_raw_parts(ptr.as_ptr(), metadata.length()) as *const _
    }

    #[inline]
    fn owned_from_parts(ptr: NonNull<Self::Pointer>, metadata: &Metadata) -> Self::Owned {
        match metadata.kind() {
            // If we have a reference, well, then yeah, we need to clone to `Vec<T>`. We own nothing so there's nothing
            // to drop.
            Kind::Borrowed => {
                let s = unsafe { &*Self::borrowed_from_parts(ptr, &metadata) };
                s.to_vec()
            }
            // We're reconstituting the `Vec<T>` directly from the backing storage.
            Kind::Owned => unsafe {
                Vec::from_raw_parts(ptr.as_ptr(), metadata.length(), metadata.capacity())
            },
            // We specifically do _not_ forget the `Arc<[T]>` here, like we do in `clone_from_parts`.
            //
            // This method overall is called when `Cow2` is being consumed.  In the case of `Cow2` owning the vector,
            // letting the `Drop` impl run would try to deallocate that vector, which obviously wouldn't fly, so we
            // ensure thre `Drop` impl doesn't run... but that doesn't work here, because we're not able to consume
            // anything from `Arc<[T]>`, so we only need a reference to call `to_vec` but we can't leave our
            // `Arc<[T]>` dangling... so we have to make sure it drops here.
            Kind::Shared => {
                let s = unsafe { Arc::from_raw(Self::borrowed_from_parts(ptr, metadata)) };
                s.to_vec()
            }
        }
    }

    #[inline]
    fn clone_from_parts(
        ptr: NonNull<Self::Pointer>,
        metadata: &Metadata,
    ) -> (NonNull<Self::Pointer>, Metadata) {
        match metadata.kind() {
            // As we're operating on a reference, `Cow2` is bound to the lifetime of tthat source reference. In turn, we
            // can safely the same pointer/metadata to that reference for the clone of `Cow2` so long as the lifetimes
            // as identical, as the clone cannot go out-of-scope any later than the original `Cow2` will.
            Kind::Borrowed => (ptr, *metadata),
            // Small deduplication of code by using the same code as we would to get an owned version of a referenced
            // `Cow2`, given that both a referenced and owned version ultimately point to a [u8].
            Kind::Owned => Self::owned_into_parts(Self::owned_from_parts(ptr, metadata)),
            // We have to reconstruct the `Arc` so we can correctly clone it but we _also_ have to make sure that we
            // forget `original` so that we don't drop it early and invalidate the actual string being pointed to.
            Kind::Shared => {
                let original = unsafe { Arc::from_raw(Self::borrowed_from_parts(ptr, metadata)) };
                let new = Arc::clone(&original);

                // SAFETY: The backing `Arc<[T]>` will be dropped via the `Drop` impl for `Cow2`.
                std::mem::forget(original);
                Self::shared_into_parts(new)
            }
        }
    }

    #[inline]
    fn drop_from_parts(ptr: NonNull<Self::Pointer>, metadata: &Metadata) {
        match metadata.kind() {
            // References don't own anything, so there's nothing to drop.
            Kind::Borrowed => {}
            // We originally took in a `Vec<T>`, so just reconstitute it.
            Kind::Owned => {
                let owned = unsafe {
                    Vec::from_raw_parts(ptr.as_ptr(), metadata.length(), metadata.capacity())
                };
                drop(owned);
            }
            // We just need to reconstitute the `Arc<[T]>` so it can run its own drop logic.
            Kind::Shared => {
                let arc = unsafe { Arc::from_raw(Self::borrowed_from_parts(ptr, metadata)) };
                drop(arc);
            }
        }
    }
}

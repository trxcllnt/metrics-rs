use std::{
    marker::PhantomData,
    mem::ManuallyDrop,
    ops::Deref,
    ptr::{slice_from_raw_parts, NonNull},
    sync::Arc,
};

use crate::Label;

// As `NonInlined`/`Inlined` are the same size, and share an overlap, the maximum amount of data we can store is the
// size of two `usize`, minus one byte that we use for holding the length of the inlined string.
const MAX_INLINE_DATA_LEN: usize = (2 * std::mem::size_of::<usize>()) - 1;

#[derive(Clone, Copy)]
enum Kind {
    Owned,
    Borrowed,
    Shared,
}

/// A clone-on-write smart pointer with an optimized memory layout, based on `beef`.
///
/// # Strings, strings everywhere
///
/// In `metrics`, strings are arguably the most common data type used despite fundamentally dealing with numerical
/// measurements. Both the name of a metric, and its labels, are compromised a strings: emitting a metric may involve
/// one string, or 10 strings. Even further, many of these strings tend to be used over and over during the life of the
/// process.
///
/// In over to provide high performance, and to help avoid making constant, small allocations, using a "clone-on-write"
/// smart pointer allows us to represent a logical data type -- such as a string -- in multiple forms, depending on
/// which is available, and allows for seamless access to that data, whether its immutable access of creating an owned version.
///
/// # Why not `std::borrow::Cow`?
///
/// Typically, those writing Rust may reach for `std::borrow::Cow`, which already works well in many cases. However,
/// `metrics` strives to provide minimal overhead where possible, and so `std::borrow::Cow` falls down in one particular
/// way: it uses an enum representation which consumes an additional word of storage.
///
/// As an example, let's look at strings. A string in `std::borrow::Cow` implies that `T` is `str`, and the owned
/// version of `str` is simply `String`. Thus, for `std::borrow::Cow`, the in-memory layout looks like this:
///
/// ```text
///                                                            Padding
///                                                               |
///                                                               v
///                       +--------------+-------------+--------------+--------------+
/// stdlib Cow::Borrowed: |   Enum Tag   |   Pointer   |    Length    |   XXXXXXXX   |
///                       +--------------+-------------+--------------+--------------+
///                       +--------------+-------------+--------------+--------------+
/// stdlib Cow::Owned:    |   Enum Tag   |   Pointer   |    Length    |   Capacity   |
///                       +--------------+-------------+--------------+--------------+
/// ```
///
/// Just as `beef` does, we encode the notion of borrowed vs owned into the the length and capacity fields directly,
/// and use a struct, which avoids needing an implicit or explicit discriminant field:
///
/// ```text
///                         +-------------+--------------+----------------+
/// metrics Cow (borrowed): |   Pointer   |  Length (N)  |  Capacity (0)  |
///                         +-------------+--------------+----------------+
///                         +-------------+--------------+----------------+
/// stdlib Cow (owned):     |   Pointer   |  Length (N)  |  Capacity (N)  |
///                         +-------------+--------------+----------------+
/// ```
///
/// # Why not `beef`?
///
/// Up until this point, it might not be clear why we didn't just use `beef`. And indeed, we've already admitted that
/// this design is fundamentally based on `beef`. Crucially, however, `beef` did not/still does not support `const`
/// construction for generic slices. Remember how we mentioned labels? The labels of a metric `are `[Label]`
/// under-the-hood, and so without a way to construct them in a `const` fashion, our previous work to allow entirely
/// static keys would not be possible.
///
/// Thus, we forked `beef` and copied into directly into `metrics` so that we could write a specialized `const`
/// constructor for `[Label]`.
///
/// # What we do that `beef` doesn't do
///
/// It was already enough to use our own implementation for the specialized `const` capabilities, but we've taken things
/// even further in two key ways: support for `Arc`-wrapped values, and inlined strings.
///
/// ## `Arc`-wrapped values
///
/// For many strings, there is still a desire to share them cheaply even when they are constructed at run-time.
/// Remember, cloning a `Cow` of an owned value means cloning the value itself, so we need another level of indirection
/// to allow the cheap sharing, which is where `Arc<T>` comes in.
///
/// Users can construct a `Arc<T>`, whether `T` is lines up with the `T` of `metrics::Cow2`, and use that as the initial
/// value instead. When `Cow2` is cloned, we instead cloning the underlying `Arc<T>`, avoiding a new allocation.
/// `Arc<T>` still handles all of the normal logic necessary to know when the wrapped value must be dropped, and how
/// many live references to the value that there are, and so on.
///
/// We handle this by relying on an invariant of `Vec<T>`: it never allocates more than `isize::MAX` [1]. This lets us
/// derive the following truth table of the valid combinations of length/capacity:
///
/// ```text
///                           Length         Capacity
///                     +---------------+----------------+
/// Borrowed (&T):      |       N       |        0       |
///                     +---------------+----------------+
/// Owned (T::ToOwned): |       N       | M < usize::MAX |
///                     +---------------+----------------+
/// Shared (Arc<T>):    |       N       |   usize::MAX   |
///                     +---------------+----------------+
/// ```
///
/// As we only implement `Cow2` for types where their owned variants are either explicitly or implicitly backed by
/// `Vec<_>`, we know that our capacity will never be `usize::MAX`, as it is limited to `isize::MAX`, and thus we can
/// safely encode our "shared" state within the capacity field.
///
/// ## Inlined strings
///
/// As `Cow2` is primarily meant for string data, we never want to leave an optimization on the table, and another trick
/// we added is string inlining.
///
/// String inlining is based on the concept of reinterpreting the memory used for a type to use it for raw string
/// storage in certain cases.
///
/// Fundamentally, `Cow2` has a specific size of three words, or three `usize` values: 24 bytes on a 64-bit platform,
/// for example. Instead of looking at `Cow2` as three `usize`-sized fields, what if we looked at it as a single `[u8;
/// 24]` field? We could then store the raw bytes of a string that was short enough directly in the memory for `Cow2`.
/// This lets us avoid pointer chasing when getting a reference to the string through `Cow2`, and it lets us avoid
/// having to make a new allocation when cloning an owned version of `Cow2`.
///
/// Unfortunately, we can't just blindly store a 24-byte string inside `Cow2`, as we need some of those bytes to act as
/// our discriminant -- is this an inlined string or not? -- as well as to hold the length of the string, so we can
/// properly reconstruct the fundamental `&[u8]` that backs the `str`. This means we're limited to inlining strings up
/// to a length of `2*N-1`: our normal pointer field becomes optional (its discriminant is our now our
/// inlined/non-inlined discriminant) which means we lose a word, but since there is no known platform that Rust
/// supports where two words would be over 255 bytes total, we can use a single `u8` to hold our string length.
///
/// Practically, this means strings up to 15 bytes can be inlined on 64-bit platforms, while 32-bit platforms are
/// limited to 7 bytes.
///
/// # Notes
///
/// [1] - technically, `Vec<T>` can have a capacity greater than `isize::MAX` when storing zero-sized types, but we
/// don't do that here, so we always enforce that an owned version's capacity cannot be `usize::MAX` when constructing `Cow2`
pub struct Cow2<'a, T: Cow2able + ?Sized + 'a> {
    /// Pointer to data.
    ptr: Option<NonNull<T::Pointer>>,

    /// Inner state: either pointer metadata (non-inlined) or inlined data.
    inner: Inner,

    /// Lifetime marker.
    marker: PhantomData<&'a T>,
}

/// Smart pointer state.
///
/// Used to differentiate both whether or not the smart pointer is inlining a value, but also the specific data of each
/// discriminant i.e. the data for an inlined value vs the length/capacity of a non-inlined value.
#[derive(Clone, Copy)]
pub union Inner {
    non_inlined: NonInlined,
    inlined: Inlined,
}

impl Inner {
    const fn non_inlined(metadata: Metadata) -> Self {
        Self { non_inlined: NonInlined(metadata) }
    }

    const fn inlined(length: u8, data: [u8; MAX_INLINE_DATA_LEN]) -> Self {
        Self { inlined: Inlined { length, data } }
    }
}

#[repr(transparent)]
#[derive(Clone, Copy)]
struct NonInlined(Metadata);

#[repr(C)]
#[derive(Clone, Copy)]
struct Inlined {
    /// Length of our inlined string.
    length: u8,

    /// String data.
    data: [u8; MAX_INLINE_DATA_LEN],
}

impl<T> Cow2<'_, T>
where
    T: Cow2able + ?Sized,
{
    fn non_inlined(ptr: NonNull<T::Pointer>, metadata: Metadata) -> Self {
        Self { ptr: Some(ptr), inner: Inner::non_inlined(metadata), marker: PhantomData }
    }

    /// Creates a smart pointer around an owned value.
    pub fn from_owned(owned: T::Owned) -> Self {
        let (ptr, metadata) = T::owned_into_parts(owned);

        // This check is partially to guard against the semantics of `Vec<T>` changing in the future, and partially to
        // ensure that we don't somehow implement `Cow2able` for a type where its owned version is backed by a vector of
        // ZSTs, where the capacity could _legitimately_ be `usize::MAX`.
        if metadata.capacity() == usize::MAX {
            panic!("Invalid capacity of `usize::MAX` for owned value.");
        }

        Self::non_inlined(ptr, metadata)
    }

    /// Creates a smart pointer around a shared value.
    pub fn from_shared(arc: Arc<T>) -> Self {
        let (ptr, metadata) = T::shared_into_parts(arc);

        Self::non_inlined(ptr, metadata)
    }

    /// Extracts the owned data.
    ///
    /// Clones the data if it is not already owned.
    pub fn into_owned(self) -> <T as ToOwned>::Owned {
        // We have to ensure that the `Drop` impl does _not_ run because we're taking ownership back in the case of
        // holding an owned value. `owned_from_parts` handles any necessary dropping that must occur i.e. if we're holding
        // an `Arc<T>`.
        let cow = ManuallyDrop::new(self);

        T::owned_from_parts(cow.ptr, &cow.inner)
    }
}

impl<'a, T> Cow2<'a, T>
where
    T: Cow2able + ?Sized,
{
    /// Creates a smart pointer around a borrowed value.
    pub fn from_borrowed(borrowed: &'a T) -> Self {
        let (ptr, metadata) = T::borrowed_into_parts(borrowed);

        Self::non_inlined(ptr, metadata)
    }
}

impl<T> Deref for Cow2<'_, T>
where
    T: Cow2able + ?Sized,
{
    type Target = T;

    fn deref(&self) -> &Self::Target {
        let borrowed_ptr = T::borrowed_from_parts(self.ptr, &self.inner);
        unsafe { borrowed_ptr.as_ref().unwrap() }
    }
}

impl<T> Clone for Cow2<'_, T>
where
    T: Cow2able + ?Sized,
{
    fn clone(&self) -> Self {
        let (ptr, inner) = T::clone_from_parts(self.ptr, &self.inner);
        Self { ptr, inner, marker: PhantomData }
    }
}

impl<T> Drop for Cow2<'_, T>
where
    T: Cow2able + ?Sized,
{
    fn drop(&mut self) {
        T::drop_from_parts(self.ptr, &self.inner);
    }
}

// Implementations of constant functions for creating `Cow` via static strings, static string
// slices, and static label slices.
impl<'a> Cow2<'a, str> {
    pub const fn const_str(val: &'a str) -> Self {
        // SAFETY: We can never create a null pointer by casting a reference to a pointer.
        let ptr = unsafe { NonNull::new_unchecked(val.as_ptr() as *mut _) };
        let metadata = Metadata::borrowed(val.len());

        Self { ptr: Some(ptr), inner: Inner::non_inlined(metadata), marker: PhantomData }
    }
}

impl<'a> Cow2<'a, [Label]> {
    pub const fn const_slice(val: &'a [Label]) -> Cow2<'a, [Label]> {
        // SAFETY: We can never create a null pointer by casting a reference to a pointer.
        let ptr = unsafe { NonNull::new_unchecked(val.as_ptr() as *mut _) };
        let metadata = Metadata::borrowed(val.len());

        Self { ptr: Some(ptr), inner: Inner::non_inlined(metadata), marker: PhantomData }
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

#[repr(C)]
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

    #[inline]
    const fn shared(length: usize) -> Metadata {
        Metadata(length, usize::MAX)
    }

    #[inline]
    const fn borrowed(len: usize) -> Metadata {
        Metadata(len, 0)
    }

    #[inline]
    const fn owned(len: usize, capacity: usize) -> Metadata {
        Metadata(len, capacity)
    }
}

pub trait Cow2able: ToOwned {
    type Pointer;

    fn borrowed_into_parts(&self) -> (NonNull<Self::Pointer>, Metadata);
    fn owned_into_parts(owned: <Self as ToOwned>::Owned) -> (NonNull<Self::Pointer>, Metadata);
    fn shared_into_parts(arc: Arc<Self>) -> (NonNull<Self::Pointer>, Metadata);

    fn borrowed_from_parts(ptr: Option<NonNull<Self::Pointer>>, inner: &Inner) -> *const Self;
    fn owned_from_parts(
        ptr: Option<NonNull<Self::Pointer>>,
        inner: &Inner,
    ) -> <Self as ToOwned>::Owned;
    fn clone_from_parts(
        ptr: Option<NonNull<Self::Pointer>>,
        inner: &Inner,
    ) -> (Option<NonNull<Self::Pointer>>, Inner);
    fn drop_from_parts(ptr: Option<NonNull<Self::Pointer>>, inner: &Inner);
}

impl Cow2able for str {
    type Pointer = u8;

    #[inline]
    fn borrowed_into_parts(&self) -> (NonNull<Self::Pointer>, Metadata) {
        let ptr = unsafe { NonNull::new_unchecked(self.as_ptr() as *mut _) };
        let metadata = Metadata::borrowed(self.len());
        (ptr, metadata)
    }

    #[inline]
    fn owned_into_parts(owned: Self::Owned) -> (NonNull<Self::Pointer>, Metadata) {
        // We need to go through `Vec<T>` here to get provenance for the entire allocation instead of just the
        // initialized parts.
        let mut owned = ManuallyDrop::new(owned.into_bytes());
        let ptr = unsafe { NonNull::new_unchecked(owned.as_mut_ptr()) };
        let metadata = Metadata::owned(owned.len(), owned.capacity());
        (ptr, metadata)
    }

    #[inline]
    fn shared_into_parts(arc: Arc<Self>) -> (NonNull<Self::Pointer>, Metadata) {
        let metadata = Metadata::shared(arc.len());
        let ptr = unsafe { NonNull::new_unchecked(Arc::into_raw(arc) as *mut _) };
        (ptr, metadata)
    }

    #[inline]
    fn borrowed_from_parts(ptr: Option<NonNull<Self::Pointer>>, inner: &Inner) -> *const Self {
        // When the pointer is `None`, we're inlining the string. Otherwise, it's not inlined.
        match ptr {
            None => {
                let length = unsafe { inner.inlined.length };
                let data = unsafe { &inner.inlined.data as *const _ };
                slice_from_raw_parts(data, length as usize) as *const _
            }
            Some(ptr) => {
                let metadata = unsafe { inner.non_inlined.0 };
                slice_from_raw_parts(ptr.as_ptr(), metadata.length()) as *const _
            }
        }
    }

    #[inline]
    fn owned_from_parts(
        ptr: Option<NonNull<Self::Pointer>>,
        inner: &Inner,
    ) -> <Self as ToOwned>::Owned {
        // When the pointer is `None`, we're inlining the string. Otherwise, it's not inlined.
        match ptr {
            None => {
                // We copy the logic of getting an owned version of a borrowed string, which is just to get a valid
                // `&str` and then call `to_string`.
                let s = unsafe { &*Self::borrowed_from_parts(ptr, inner) };
                s.to_string()
            }

            Some(ptr) => {
                let metadata = unsafe { inner.non_inlined.0 };
                match metadata.kind() {
                    // If we have a reference, well, then yeah, we need to clone to `String` via `to_string`. We own nothing so
                    // there's nothing to drop.
                    Kind::Borrowed => {
                        let s = unsafe { &*Self::borrowed_from_parts(Some(ptr), inner) };
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
                        let s =
                            unsafe { Arc::from_raw(Self::borrowed_from_parts(Some(ptr), inner)) };
                        s.to_string()
                    }
                }
            }
        }
    }

    #[inline]
    fn clone_from_parts(
        ptr: Option<NonNull<Self::Pointer>>,
        inner: &Inner,
    ) -> (Option<NonNull<Self::Pointer>>, Inner) {
        // When the pointer is `None`, we're inlining the string. Otherwise, it's not inlined.
        match ptr {
            // Just copy the entire `Inner` as-is, since we're inlined.
            None => (None, *inner),

            Some(ptr) => {
                let metadata = unsafe { inner.non_inlined.0 };
                match metadata.kind() {
                    // As we're operating on a reference, `Cow2` is bound to the lifetime of tthat source reference. In turn, we
                    // can safely the same pointer/metadata to that reference for the clone of `Cow2` so long as the lifetimes
                    // as identical, as the clone cannot go out-of-scope any later than the original `Cow2` will.
                    Kind::Borrowed => (Some(ptr), Inner::non_inlined(metadata)),

                    // When we have an owned string, we first take a reference to it and check its length. If it can be
                    // inlined, we do that instead of cloning the string and giving back yet another owned `Cow2`, since
                    // there's no point allocating something small enough to be inlined.
                    Kind::Owned => {
                        let s = unsafe { &*Self::borrowed_from_parts(Some(ptr), inner) };

                        let sbuf = s.as_bytes();
                        let slen = sbuf.len();
                        if slen <= MAX_INLINE_DATA_LEN {
                            let mut data = [0u8; MAX_INLINE_DATA_LEN];
                            (&mut data[..slen]).copy_from_slice(sbuf);

                            let length = slen as u8;

                            (None, Inner::inlined(length, data))
                        } else {
                            let (ptr, metadata) = Self::owned_into_parts(s.to_string());
                            (Some(ptr), Inner::non_inlined(metadata))
                        }
                    }

                    // We have to reconstruct the `Arc` so we can correctly clone it but we _also_ have to make sure that we
                    // forget `original` so that we don't drop it early and invalidate the actual string being pointed to.
                    Kind::Shared => {
                        let original =
                            unsafe { Arc::from_raw(Self::borrowed_from_parts(Some(ptr), inner)) };
                        let new = Arc::clone(&original);

                        // SAFETY: The backing `Arc<str>` will be dropped via the `Drop` impl for `Cow2`.
                        std::mem::forget(original);

                        let (ptr, metadata) = Self::shared_into_parts(new);
                        (Some(ptr), Inner::non_inlined(metadata))
                    }
                }
            }
        }
    }

    #[inline]
    fn drop_from_parts(ptr: Option<NonNull<Self::Pointer>>, inner: &Inner) {
        // When the pointer is `None`, we're inlining the string. Otherwise, it's not inlined. Since we have nothing to
        // drop when inlined, focus on the non-inlined case here.
        if let Some(ptr) = ptr {
            let metadata = unsafe { inner.non_inlined.0 };
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
                    let arc = unsafe { Arc::from_raw(Self::borrowed_from_parts(Some(ptr), inner)) };
                    drop(arc);
                }
            }
        }
    }
}

impl<T> Cow2able for [T]
where
    T: Clone,
{
    type Pointer = T;

    #[inline]
    fn borrowed_into_parts(&self) -> (NonNull<Self::Pointer>, Metadata) {
        let ptr = unsafe { NonNull::new_unchecked(self.as_ptr() as *mut _) };
        let metadata = Metadata::borrowed(self.len());
        (ptr, metadata)
    }

    #[inline]
    fn owned_into_parts(owned: <Self as ToOwned>::Owned) -> (NonNull<Self::Pointer>, Metadata) {
        let mut owned = ManuallyDrop::new(owned);
        let ptr = unsafe { NonNull::new_unchecked(owned.as_mut_ptr()) };
        let metadata = Metadata::owned(owned.len(), owned.capacity());
        (ptr, metadata)
    }

    #[inline]
    fn shared_into_parts(arc: Arc<Self>) -> (NonNull<Self::Pointer>, Metadata) {
        let metadata = Metadata::shared(arc.len());
        let ptr = unsafe { NonNull::new_unchecked(Arc::into_raw(arc) as *mut _) };
        (ptr, metadata)
    }

    #[inline]
    fn borrowed_from_parts(ptr: Option<NonNull<Self::Pointer>>, inner: &Inner) -> *const Self {
        // SAFETY: Only `str` can ever be inlined, not `[str]`, so we would panic on unwrapping `ptr` before
        // accessing `inner`, and so we cannot perform an invalid access of `inner`: if `ptr` is `Some(...)`, then
        // `self.non_inlined` must be initialized and valid.
        let ptr = ptr.expect("not an inlinable type; `ptr` must be `Some(..)`");
        let metadata = unsafe { inner.non_inlined.0 };

        slice_from_raw_parts(ptr.as_ptr(), metadata.length()) as *const _
    }

    #[inline]
    fn owned_from_parts(
        ptr: Option<NonNull<Self::Pointer>>,
        inner: &Inner,
    ) -> <Self as ToOwned>::Owned {
        // SAFETY: Only `str` can ever be inlined, not `[str]`, so we would panic on unwrapping `ptr` before
        // accessing `inner`, and so we cannot perform an invalid access of `inner`: if `ptr` is `Some(...)`, then
        // `self.non_inlined` must be initialized and valid.
        let ptr = ptr.expect("not an inlinable type; `ptr` must be `Some(..)`");
        let metadata = unsafe { inner.non_inlined.0 };

        match metadata.kind() {
            // If we have a reference, well, then yeah, we need to clone to `Vec<T>`. We own nothing so there's nothing
            // to drop.
            Kind::Borrowed => {
                let s = unsafe { &*Self::borrowed_from_parts(Some(ptr), inner) };
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
                let s = unsafe { Arc::from_raw(Self::borrowed_from_parts(Some(ptr), inner)) };
                s.to_vec()
            }
        }
    }

    #[inline]
    fn clone_from_parts(
        ptr: Option<NonNull<Self::Pointer>>,
        inner: &Inner,
    ) -> (Option<NonNull<Self::Pointer>>, Inner) {
        // SAFETY: Only `str` can ever be inlined, not `[str]`, so we would panic on unwrapping `ptr` before
        // accessing `inner`, and so we cannot perform an invalid access of `inner`: if `ptr` is `Some(...)`, then
        // `self.non_inlined` must be initialized and valid.
        let ptr = ptr.expect("not an inlinable type; `ptr` must be `Some(..)`");
        let metadata = unsafe { inner.non_inlined.0 };

        match metadata.kind() {
            // As we're operating on a reference, `Cow2` is bound to the lifetime of tthat source reference. In turn, we
            // can safely the same pointer/metadata to that reference for the clone of `Cow2` so long as the lifetimes
            // as identical, as the clone cannot go out-of-scope any later than the original `Cow2` will.
            Kind::Borrowed => (Some(ptr), Inner::non_inlined(metadata)),

            // Small deduplication of code by using the same code as we would to get an owned version of a referenced
            // `Cow2`, given that both a referenced and owned version ultimately point to the same type of thing.
            Kind::Owned => {
                let (ptr, metadata) =
                    Self::owned_into_parts(Self::owned_from_parts(Some(ptr), inner));
                (Some(ptr), Inner::non_inlined(metadata))
            }

            // We have to reconstruct the `Arc` so we can correctly clone it but we _also_ have to make sure that we
            // forget `original` so that we don't drop it early and invalidate the actual value being pointed to.
            Kind::Shared => {
                let original =
                    unsafe { Arc::from_raw(Self::borrowed_from_parts(Some(ptr), inner)) };
                let new = Arc::clone(&original);

                // SAFETY: The backing `Arc<[T]>` will be dropped via the `Drop` impl for `Cow2`.
                std::mem::forget(original);

                let (ptr, metadata) = Self::shared_into_parts(new);
                (Some(ptr), Inner::non_inlined(metadata))
            }
        }
    }

    #[inline]
    fn drop_from_parts(ptr: Option<NonNull<Self::Pointer>>, inner: &Inner) {
        // SAFETY: Only `str` can ever be inlined, not `[str]`, so we would panic on unwrapping `ptr` before
        // accessing `inner`, and so we cannot perform an invalid access of `inner`: if `ptr` is `Some(...)`, then
        // `self.non_inlined` must be initialized and valid.
        let ptr = ptr.expect("not an inlinable type; `ptr` must be `Some(..)`");
        let metadata = unsafe { inner.non_inlined.0 };

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
                let arc = unsafe { Arc::from_raw(Self::borrowed_from_parts(Some(ptr), inner)) };
                drop(arc);
            }
        }
    }
}

//! Metric recency.
//!
//! `Recency` deals with the concept of removing metrics that have not been updated for a certain
//! amount of time.  In some use cases, metrics are tied to specific labels which are short-lived,
//! such as labels referencing a date or a version of software.  When these labels change, exporters
//! may still be emitting those older metrics which are no longer relevant.  In many cases, a
//! long-lived application could continue tracking metrics such that the unique number of metrics
//! grows until a significant portion of memory is required to track them all, even if the majority
//! of them are no longer used.
//!
//! As metrics are typically backed by atomic storage, exporters don't see the individual changes to
//! a metric, and so need a way to measure if a metric has changed since the last time it was
//! observed.  This could potentially be achieved by observing the value directly, but metrics like
//! gauges can be updated in such a way that their value is the same between two observations even
//! though it had actually been changed in between.
//!
//! We solve for this by tracking the generation of a metric, which represents the number of times
//! it has been modified. In doing so, we can compare the generation of a metric between
//! observations, which only ever increases monotonically.  This provides a universal mechanism that
//! works for all metric types.
//!
//! `Recency` uses the generation of a metric, along with a measurement of time when a metric is
//! observed, to build a complete picture that allows deciding if a given metric has gone "idle" or
//! not, and thus whether it should actually be deleted.
use std::{borrow::Borrow, marker::PhantomData, sync::atomic::{AtomicUsize, Ordering}};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;
use std::{collections::HashMap, ops::DerefMut};

use metrics::{Counter, CounterFn, Gauge, GaugeFn, Histogram, HistogramFn};
use quanta::{Clock, Instant};

use crate::Hashable;
use crate::{
    kind::MetricKindMask,
    registry::{AtomicStorage, Registry, Storage},
    MetricKind,
};

/// The generation of a metric.
///
/// Generations are opaque and are not meant to be used directly, but meant to be used as a
/// comparison amongst each other in terms of ordering.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Generation(usize);

/// Generation tracking for a metric.
///
/// Holds a generic interior value, and provides way to access the value such that each access
/// increments the "generation" of the value.  This provides a means to understand if the value has
/// been updated since the last time it was observed.
///
/// For example, if a gauge was observed to be X at one point in time, and then observed to be X
/// again at a later point in time, it could have changed in between the two observations.  It also
/// may not have changed, and thus `Generational` provides a way to determine if either of these
/// events occurred.
#[derive(Clone)]
pub struct Generational<T> {
    inner: T,
    gen: Arc<AtomicUsize>,
}

impl<T> Generational<T> {
    /// Creates a new `Generational<T>`.
    fn new(inner: T) -> Generational<T> {
        Generational { inner, gen: Arc::new(AtomicUsize::new(0)) }
    }

    /// Gets a reference to the inner value.
    pub fn get_inner(&self) -> &T {
        &self.inner
    }

    /// Gets the current generation.
    pub fn get_generation(&self) -> Generation {
        Generation(self.gen.load(Ordering::Acquire))
    }

    /// Acquires a reference to the inner value, and increments the generation.
    pub fn with_increment<F, V>(&self, f: F) -> V
    where
        F: Fn(&T) -> V,
    {
        let result = f(&self.inner);
        let _ = self.gen.fetch_add(1, Ordering::AcqRel);
        result
    }
}

impl<T> CounterFn for Generational<T>
where
    T: CounterFn,
{
    fn increment(&self, value: u64) {
        self.with_increment(|c| c.increment(value))
    }

    fn absolute(&self, value: u64) {
        self.with_increment(|c| c.absolute(value))
    }
}

impl<T> GaugeFn for Generational<T>
where
    T: GaugeFn,
{
    fn increment(&self, value: f64) {
        self.with_increment(|g| g.increment(value))
    }

    fn decrement(&self, value: f64) {
        self.with_increment(|g| g.decrement(value))
    }

    fn set(&self, value: f64) {
        self.with_increment(|g| g.set(value))
    }
}

impl<T> HistogramFn for Generational<T>
where
    T: HistogramFn,
{
    fn record(&self, value: f64) {
        self.with_increment(|h| h.record(value))
    }
}

impl<T> From<Generational<T>> for Counter
where
    T: CounterFn + Send + Sync + 'static,
{
    fn from(inner: Generational<T>) -> Self {
        Counter::from_arc(Arc::new(inner))
    }
}

impl<T> From<Generational<T>> for Gauge
where
    T: GaugeFn + Send + Sync + 'static,
{
    fn from(inner: Generational<T>) -> Self {
        Gauge::from_arc(Arc::new(inner))
    }
}

impl<T> From<Generational<T>> for Histogram
where
    T: HistogramFn + Send + Sync + 'static,
{
    fn from(inner: Generational<T>) -> Self {
        Histogram::from_arc(Arc::new(inner))
    }
}

/// Generational metric storage.
///
/// Tracks the "generation" of a metric, which is used to detect updates to metrics where the value
/// otherwise would not be sufficient to be used as an indicator.
pub struct GenerationalStorage<S> {
    inner: S,
}

impl<S> GenerationalStorage<S> {
    /// Creates a new [`GenerationalStorage`].
    ///
    /// This wraps the given `storage` and provides generational semantics on top of it.
    pub fn new(storage: S) -> Self {
        Self { inner: storage }
    }
}

impl<K, S: Storage<K>> Storage<K> for GenerationalStorage<S> {
    type Counter = Generational<S::Counter>;
    type Gauge = Generational<S::Gauge>;
    type Histogram = Generational<S::Histogram>;

    fn counter(&self, key: &K) -> Self::Counter {
        Generational::new(self.inner.counter(key))
    }

    fn gauge(&self, key: &K) -> Self::Gauge {
        Generational::new(self.inner.gauge(key))
    }

    fn histogram(&self, key: &K) -> Self::Histogram {
        Generational::new(self.inner.histogram(key))
    }
}

/// Generational atomic metric storage.
///
/// `GenerationalAtomicStorage` is based on [`AtomicStorage`], but additionally tracks the
/// "generation" of a metric, which is used to detect updates to metrics where the value otherwise
/// would not be sufficient to be used as an indicator.
pub type GenerationalAtomicStorage = GenerationalStorage<AtomicStorage>;

impl GenerationalAtomicStorage {
    /// Creates a [`GenerationalStorage`] that uses [`AtomicStorage`] as its underlying storage.
    pub fn atomic() -> Self {
        Self { inner: AtomicStorage }
    }
}

#[derive(Clone, Eq, Hash, PartialEq)]
struct KeyWithKind<K> {
    kind: MetricKind,
    key: K,
}

pub enum MetricState {
    /// The metric is still referenced in a way in which it could be updated in the future, but has
    /// currently not seen an update within the recency window, and should be marked as idle to
    /// allow it to be skipped / ignored when generating exporter output, etc.
    Idle,

    /// The metric is no longer referenced in a way in which it could be updated in the future, so
    /// it can safely be deleted from the registry entirely after any necessary final processing.
    Dead,
}

/// Tracks recency of metric updates by their registry generation and time.
///
/// In many cases, a user may have a long-running process where metrics are stored over time using
/// labels that change for some particular reason, leaving behind versions of that metric with
/// labels that are no longer relevant to the current process state.  This can lead to cases where
/// metrics that no longer matter are still present in rendered output, adding bloat.
///
/// When coupled with [`Registry`], [`Recency`] can be used to track when the last update to a
/// metric has occurred for the purposes of removing idle metrics from the registry. Idle metrics
/// can be skipped to avoid increasing the output of an exporter in an unbounded fashion.
///
/// [`Recency`] is separate from [`Registry`] specifically to avoid imposing any slowdowns when
/// tracking recency does not matter, despite their otherwise tight coupling.
pub struct Recency<K, S> {
    idle_timeout: Option<Duration>,
    mask: MetricKindMask,
    clock: Clock,
    inner: Mutex<HashMap<KeyWithKind<K>, (Generation, Instant)>>,

    // TODO: different methods for different storage types so we can enhance the detection of
    // whether or not the metric is simply idle or if it's no longer referenced at all
    _storage: PhantomData<S>,
}

impl<K, S> Recency<K, S>
where
    K: Clone + Eq + Hashable,
{
    /// Creates a new [`Recency`].
    ///
    /// If `idle_timeout` is `None`, no recency checking will occur.  Otherwise, any metric that has
    /// not been updated for longer than `idle_timeout` will be subject to being marked as idle the
    /// next time the metric is checked.
    ///
    /// The provided `clock` is used for tracking time, while `mask` controls which metrics are
    /// covered by the recency logic.  For example, if `mask` only contains counters and histograms,
    /// then gauges will not be considered for recency, and thus will never be marked idle.
    ///
    /// Refer to the documentation for [`MetricKindMask`](crate::MetricKindMask) for more
    /// information on defining a metric kind mask.
    pub fn new(clock: Clock, mask: MetricKindMask, idle_timeout: Option<Duration>) -> Self {
        Recency { clock, mask, idle_timeout, inner: Mutex::new(HashMap::new()), _storage: PhantomData }
    }

    /// Checks if the given metric is idle or not based on the last time it was observed.
    ///
    /// If the given metric has not yet been seen, it will be tracked and considered active. If the
    /// given metric has been seen, but not updated since the last time it was observed, and the
    /// last update was greater than the idle timeout, the metric is considered idle. Otherwise, it
    /// is considered active.
    ///
    /// Otherwise, the metric is considered active.
    ///
    /// If the given key has been updated recently enough, and should continue to be stored, this
    /// method will return `true` and will update the last update time internally.  If the given key
    /// has not been updated recently enough, the key will be
    pub fn is_metric_idle(
        &self,
        kind: MetricKind,
        key: &K,
        gen: Generation,
    ) -> bool {
        match self.idle_timeout {
            Some(idle_timeout) => if self.mask.matches(kind) {
                let mut guard = self.inner.lock().unwrap_or_else(PoisonError::into_inner);
                let entries = guard.deref_mut();

                let now = self.clock.now();

                // TODO: it'd be much nicer to do some `Borrow<T>` shit here but i haven't figured
                // out how to make it workable... yet.
                let full_key = KeyWithKind { kind, key: key.clone() };
                if let Some((last_gen, last_update)) = entries.get_mut(&full_key) {
                    // If the value is the same as the latest value we have internally, and
                    // we're over the idle timeout period, then remove it and continue.
                    if *last_gen == gen {
                        // If the delete returns false, that means that our generation counter is
                        // out-of-date, and that the metric has been updated since, so we don't
                        // actually want to delete it yet.
                        (now - *last_update) > idle_timeout
                    } else {
                        // Value has changed, so mark it such.
                        *last_update = now;
                        *last_gen = gen;
                        false
                    }
                } else {
                    entries.insert(full_key, (gen, now));
                    false
                }
            } else {
                false
            },
            None => false,
        }
    }
}

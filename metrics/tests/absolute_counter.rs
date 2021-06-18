use std::sync::{Arc, atomic::{AtomicU64, Ordering}};
use metrics::{absolute_counter, GaugeValue, Key, Recorder, Unit};

#[test]
fn absolute_counter() {
    // We're testing `absolute_counter!` directly here because we have to shove a whole ton
    // of boilerplate crap into the doctests for the recorder implementation, etc.

    // Tracks all counter increments against a single atomic integer.  Only useful for this test.
    struct SingleCounterRecorder(Arc<AtomicU64>);

    impl Recorder for SingleCounterRecorder {

        fn register_counter(&self, _key: &Key, _unit: Option<Unit>, _description: Option<&'static str>) {}

        fn register_gauge(&self, _key: &Key, _unit: Option<Unit>, _description: Option<&'static str>) {}

        fn register_histogram(&self, _key: &Key, _unit: Option<Unit>, _description: Option<&'static str>) {}

        fn increment_counter(&self, _key: &Key, value: u64) {
            let _ = self.0.fetch_add(value, Ordering::SeqCst);
        }

        fn update_gauge(&self, _key: &Key, _value: GaugeValue) {}

        fn record_histogram(&self, _key: &Key, _value: f64) {}
    }

    let inner = Arc::new(AtomicU64::new(0));
    let recorder = SingleCounterRecorder(Arc::clone(&inner));
    metrics::set_boxed_recorder(Box::new(recorder))
        .expect("installing recorder should never fail");

    let values = [42, 720, 1080, 999, 2020, 869, 2021];
    for value in &values {
        absolute_counter!("my_little_counter", *value);
    }

    assert_eq!(inner.load(Ordering::SeqCst), 2021);
}
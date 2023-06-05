use metrics::{Counter, Gauge, Histogram, Key, KeyName, Recorder, Attribute};
use mockall::{
    mock,
    predicate::{self, eq, function},
    Predicate,
};

#[derive(Clone)]
pub enum RecorderOperation {
    SetCounterAttribute(KeyName, Box<dyn Attribute>),
    SetGaugeAttribute(KeyName, Box<dyn Attribute>),
    SetHistogramAttribute(KeyName, Box<dyn Attribute>),
    RegisterCounter(Key, Counter),
    RegisterGauge(Key, Gauge),
    RegisterHistogram(Key, Histogram),
}

impl RecorderOperation {
    fn apply_to_mock(self, mock: &mut MockBasicRecorder) {
        match self {
            RecorderOperation::SetCounterAttribute(key, attribute) => {
                expect_set_counter_attribute(mock, key, attribute)
            }
            RecorderOperation::SetGaugeAttribute(key, attribute) => {
                expect_set_gauge_attribute(mock, key, attribute)
            }
            RecorderOperation::SetHistogramAttribute(key, attribute) => {
                expect_set_histogram_attribute(mock, key, attribute)
            }
            RecorderOperation::RegisterCounter(key, counter) => {
                expect_register_counter(mock, key, counter)
            }
            RecorderOperation::RegisterGauge(key, gauge) => expect_register_gauge(mock, key, gauge),
            RecorderOperation::RegisterHistogram(key, histogram) => {
                expect_register_histogram(mock, key, histogram)
            }
        }
    }

    pub fn apply_to_recorder<R>(self, recorder: &R)
    where
        R: Recorder,
    {
        match self {
            RecorderOperation::SetCounterAttribute(key, attribute) => {
                recorder.set_counter_attribute(key, attribute);
            }
            RecorderOperation::SetGaugeAttribute(key, attribute) => {
                recorder.set_gauge_attribute(key, attribute);
            }
            RecorderOperation::SetHistogramAttribute(key, attribute) => {
                recorder.set_histogram_attribute(key, attribute);
            }
            RecorderOperation::RegisterCounter(key, _) => {
                let _ = recorder.register_counter(&key);
            }
            RecorderOperation::RegisterGauge(key, _) => {
                let _ = recorder.register_gauge(&key);
            }
            RecorderOperation::RegisterHistogram(key, _) => {
                let _ = recorder.register_histogram(&key);
            }
        }
    }
}

mock! {
    pub BasicRecorder {}

    impl Recorder for BasicRecorder {
        fn set_counter_attribute(&self, _key: KeyName, attribute: Box<dyn Attribute>);
        fn set_gauge_attribute(&self, _key: KeyName, attribute: Box<dyn Attribute>);
        fn set_histogram_attribute(&self, _key: KeyName, attribute: Box<dyn Attribute>);
        fn register_counter(&self, key: &Key) -> Counter;
        fn register_gauge(&self, key: &Key) -> Gauge;
        fn register_histogram(&self, key: &Key) -> Histogram;
    }
}

impl MockBasicRecorder {
    pub fn from_operations<O>(operations: O) -> Self
    where
        O: IntoIterator<Item = RecorderOperation>,
    {
        let mut recorder = Self::new();
        for operation in operations.into_iter() {
            operation.apply_to_mock(&mut recorder);
        }
        recorder
    }
}

pub fn expect_set_counter_attribute(
    mock: &mut MockBasicRecorder,
    key: KeyName,
    attribute: Box<dyn Attribute>,
) {
    mock.expect_set_counter_attribute()
        .times(1)
        .with(eq(key), function(move |attr: &Box<dyn Attribute>| attribute.type_id() == attr.type_id()))
        .return_const(());
}

pub fn expect_set_gauge_attribute(
    mock: &mut MockBasicRecorder,
    key: KeyName,
    attribute: Box<dyn Attribute>,
) {
    mock.expect_set_gauge_attribute()
        .times(1)
        .with(eq(key), function(move |attr: &Box<dyn Attribute>| attribute.type_id() == attr.type_id()))
        .return_const(());
}

pub fn expect_set_histogram_attribute(
    mock: &mut MockBasicRecorder,
    key: KeyName,
    attribute: Box<dyn Attribute>,
) {
    mock.expect_set_histogram_attribute()
        .times(1)
        .with(eq(key), function(move |attr: &Box<dyn Attribute>| attribute.type_id() == attr.type_id()))
        .return_const(());
}

pub fn expect_register_counter(mock: &mut MockBasicRecorder, key: Key, counter: Counter) {
    mock.expect_register_counter().times(1).with(ref_eq(key)).return_const(counter);
}

pub fn expect_register_gauge(mock: &mut MockBasicRecorder, key: Key, gauge: Gauge) {
    mock.expect_register_gauge().times(1).with(ref_eq(key)).return_const(gauge);
}

pub fn expect_register_histogram(mock: &mut MockBasicRecorder, key: Key, histogram: Histogram) {
    mock.expect_register_histogram().times(1).with(ref_eq(key)).return_const(histogram);
}

fn ref_eq<T: PartialEq>(value: T) -> impl Predicate<T> {
    predicate::function(move |item: &T| item == &value)
}

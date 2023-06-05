use crate::layers::Layer;
use aho_corasick::{AhoCorasick, AhoCorasickBuilder};
use metrics::{Counter, Gauge, Histogram, Key, KeyName, Recorder, Attribute};

/// Filters and discards metrics matching certain name patterns.
///
/// More information on the behavior of the layer can be found in [`FilterLayer`].
pub struct Filter<R> {
    inner: R,
    automaton: AhoCorasick,
}

impl<R> Filter<R> {
    fn should_filter(&self, key: &str) -> bool {
        self.automaton.is_match(key)
    }
}

impl<R: Recorder> Recorder for Filter<R> {
    fn set_counter_attribute(&self, key: KeyName, attribute: Box<dyn Attribute>) {
        if self.should_filter(key.as_str()) {
            return;
        }
        self.inner.set_counter_attribute(key, attribute)
    }

    fn set_gauge_attribute(&self, key: KeyName, attribute: Box<dyn Attribute>) {
        if self.should_filter(key.as_str()) {
            return;
        }
        self.inner.set_gauge_attribute(key, attribute)
    }


    fn set_histogram_attribute(&self, key: KeyName, attribute: Box<dyn Attribute>) {
        if self.should_filter(key.as_str()) {
            return;
        }
        self.inner.set_histogram_attribute(key, attribute)
    }

    fn register_counter(&self, key: &Key) -> Counter {
        if self.should_filter(key.name()) {
            return Counter::noop();
        }
        self.inner.register_counter(key)
    }

    fn register_gauge(&self, key: &Key) -> Gauge {
        if self.should_filter(key.name()) {
            return Gauge::noop();
        }
        self.inner.register_gauge(key)
    }

    fn register_histogram(&self, key: &Key) -> Histogram {
        if self.should_filter(key.name()) {
            return Histogram::noop();
        }
        self.inner.register_histogram(key)
    }
}

/// A layer for filtering and discarding metrics matching certain name patterns.
///
/// Uses an [Aho-Corasick][ahocorasick] automaton to efficiently match a metric key against
/// multiple patterns at once.  Patterns are matched across the entire key i.e. they are
/// matched as substrings.
///
/// If a metric key matches any of the configured patterns, it will be skipped entirely.  This
/// applies equally to metric registration and metric emission.
///
/// A number of options are exposed that control the underlying automaton, such as compilation to a
/// DFA, or case sensitivity.
///
/// [ahocorasick]: https://en.wikipedia.org/wiki/Aho–Corasick_algorithm
#[derive(Default)]
pub struct FilterLayer {
    patterns: Vec<String>,
    case_insensitive: bool,
    use_dfa: bool,
}

impl FilterLayer {
    /// Creates a [`FilterLayer`] from an existing set of patterns.
    pub fn from_patterns<P, I>(patterns: P) -> Self
    where
        P: IntoIterator<Item = I>,
        I: AsRef<str>,
    {
        FilterLayer {
            patterns: patterns.into_iter().map(|s| s.as_ref().to_string()).collect(),
            case_insensitive: false,
            use_dfa: true,
        }
    }

    /// Adds a pattern to match.
    pub fn add_pattern<P>(&mut self, pattern: P) -> &mut FilterLayer
    where
        P: AsRef<str>,
    {
        self.patterns.push(pattern.as_ref().to_string());
        self
    }

    /// Sets the case sensitivity used for pattern matching.
    ///
    /// Defaults to `false` i.e. searches are case sensitive.
    pub fn case_insensitive(&mut self, case_insensitive: bool) -> &mut FilterLayer {
        self.case_insensitive = case_insensitive;
        self
    }

    /// Sets whether or not to internally use a deterministic finite automaton.
    ///
    /// The main benefit to a DFA is that it can execute searches more quickly than a NFA (perhaps
    /// 2-4 times as fast). The main drawback is that the DFA uses more space and can take much
    /// longer to build.
    ///
    /// Enabling this option does not change the time complexity for constructing the underlying
    /// Aho-Corasick automaton (which is O(p) where p is the total number of patterns being
    /// compiled). Enabling this option does however reduce the time complexity of non-overlapping
    /// searches from O(n + p) to O(n), where n is the length of the haystack.
    ///
    /// In general, it's a good idea to enable this if you're searching a small number of fairly
    /// short patterns (~1000), or if you want the fastest possible search without regard to
    /// compilation time or space usage.
    ///
    /// Defaults to `true`.
    pub fn use_dfa(&mut self, dfa: bool) -> &mut FilterLayer {
        self.use_dfa = dfa;
        self
    }
}

impl<R> Layer<R> for FilterLayer {
    type Output = Filter<R>;

    fn layer(&self, inner: R) -> Self::Output {
        let mut automaton_builder = AhoCorasickBuilder::new();
        let automaton = automaton_builder
            .ascii_case_insensitive(self.case_insensitive)
            .dfa(self.use_dfa)
            .auto_configure(&self.patterns)
            .build(&self.patterns);
        Filter { inner, automaton }
    }
}

#[cfg(test)]
mod tests {
    use super::FilterLayer;
    use crate::{layers::Layer, test_util::*};
    use metrics::{Counter, Gauge, Histogram, attributes::Description};

    #[test]
    fn test_basic_functionality() {
        let inputs = vec![
            RecorderOperation::SetCounterAttribute(
                "tokio.loops".into(),
                Box::new(Description::from("counter desc")),
            ),
            RecorderOperation::SetGaugeAttribute(
                "hyper.bytes_read".into(),
                Box::new(Description::from("gauge desc")),
            ),
            RecorderOperation::SetHistogramAttribute(
                "hyper.response_latency".into(),
                Box::new(Description::from("histogram desc")),
            ),
            RecorderOperation::SetCounterAttribute(
                "tokio.spurious_wakeups".into(),
                Box::new(Description::from("counter desc")),
            ),
            RecorderOperation::SetGaugeAttribute(
                "bb8.pooled_conns".into(),
                Box::new(Description::from("gauge desc")),
            ),
            RecorderOperation::RegisterCounter("tokio.loops".into(), Counter::noop()),
            RecorderOperation::RegisterGauge("hyper.bytes_read".into(), Gauge::noop()),
            RecorderOperation::RegisterHistogram(
                "hyper.response_latency".into(),
                Histogram::noop(),
            ),
            RecorderOperation::RegisterCounter("tokio.spurious_wakeups".into(), Counter::noop()),
            RecorderOperation::RegisterGauge("bb8.pooled_conns".into(), Gauge::noop()),
        ];

        let expectations = vec![
            RecorderOperation::SetGaugeAttribute(
                "hyper.bytes_read".into(),
                Box::new(Description::from("gauge desc")),
            ),
            RecorderOperation::SetHistogramAttribute(
                "hyper.response_latency".into(),
                Box::new(Description::from("histogram desc")),
            ),
            RecorderOperation::RegisterGauge("hyper.bytes_read".into(), Gauge::noop()),
            RecorderOperation::RegisterHistogram(
                "hyper.response_latency".into(),
                Histogram::noop(),
            ),
        ];

        let recorder = MockBasicRecorder::from_operations(expectations);
        let filter = FilterLayer::from_patterns(&["tokio", "bb8"]);
        let filter = filter.layer(recorder);

        for operation in inputs {
            operation.apply_to_recorder(&filter);
        }
    }

    #[test]
    fn test_case_insensitivity() {
        let inputs = vec![
            RecorderOperation::SetCounterAttribute(
                "tokiO.loops".into(),
                Box::new(Description::from("counter desc")),
            ),
            RecorderOperation::SetGaugeAttribute(
                "hyper.bytes_read".into(),
                Box::new(Description::from("gauge desc")),
            ),
            RecorderOperation::SetHistogramAttribute(
                "hyper.response_latency".into(),
                Box::new(Description::from("histogram desc")),
            ),
            RecorderOperation::SetCounterAttribute(
                "Tokio.spurious_wakeups".into(),
                Box::new(Description::from("counter desc")),
            ),
            RecorderOperation::SetGaugeAttribute(
                "bB8.pooled_conns".into(),
                Box::new(Description::from("gauge desc")),
            ),
            RecorderOperation::RegisterCounter("tokiO.loops".into(), Counter::noop()),
            RecorderOperation::RegisterGauge("hyper.bytes_read".into(), Gauge::noop()),
            RecorderOperation::RegisterHistogram(
                "hyper.response_latency".into(),
                Histogram::noop(),
            ),
            RecorderOperation::RegisterCounter("Tokio.spurious_wakeups".into(), Counter::noop()),
            RecorderOperation::RegisterGauge("bB8.pooled_conns".into(), Gauge::noop()),
        ];

        let expectations = vec![
            RecorderOperation::SetGaugeAttribute(
                "hyper.bytes_read".into(),
                Box::new(Description::from("gauge desc")),
            ),
            RecorderOperation::SetHistogramAttribute(
                "hyper.response_latency".into(),
                Box::new(Description::from("histogram desc")),
            ),
            RecorderOperation::RegisterGauge("hyper.bytes_read".into(), Gauge::noop()),
            RecorderOperation::RegisterHistogram(
                "hyper.response_latency".into(),
                Histogram::noop(),
            ),
        ];

        let recorder = MockBasicRecorder::from_operations(expectations);
        let mut filter = FilterLayer::from_patterns(&["tokio", "bb8"]);
        let filter = filter.case_insensitive(true).layer(recorder);

        for operation in inputs {
            operation.apply_to_recorder(&filter);
        }
    }
}

use metrics::{counter, Key, KeyName, Label};
use metrics_tracing_context::{LabelFilter, MetricsLayer, TracingContextLayer};
use metrics_util::debugging::{DebugValue, DebuggingRecorder, Snapshotter};
use metrics_util::{layers::Layer, CompositeKey, MetricKind};
use once_cell::sync::OnceCell;
use tracing::dispatcher::{with_default, Dispatch};
use tracing::{span, Level};
use tracing_subscriber::{layer::SubscriberExt, Registry};

static RECORDER: OnceCell<()> = OnceCell::new();
static LOGIN_ATTEMPTS: &'static str = "login_attempts";
static LOGIN_ATTEMPTS_NONE: &'static str = "login_attempts_no_labels";
static LOGIN_ATTEMPTS_STATIC: &'static str = "login_attempts_static_labels";
static LOGIN_ATTEMPTS_DYNAMIC: &'static str = "login_attempts_dynamic_labels";
static LOGIN_ATTEMPTS_BOTH: &'static str = "login_attempts_static_and_dynamic_labels";
static MY_COUNTER: &'static str = "my_counter";
static USER_EMAIL: &'static [Label] = &[
    Label::from_static_parts("user", "ferris"),
    Label::from_static_parts("user.email", "ferris@rust-lang.org"),
];
static EMAIL_USER: &'static [Label] = &[
    Label::from_static_parts("user.email", "ferris@rust-lang.org"),
    Label::from_static_parts("user", "ferris"),
];
static SVC_ENV: &'static [Label] = &[
    Label::from_static_parts("service", "login_service"),
    Label::from_static_parts("env", "test"),
];
static SVC_USER_EMAIL: &'static [Label] = &[
    Label::from_static_parts("service", "login_service"),
    Label::from_static_parts("user", "ferris"),
    Label::from_static_parts("user.email", "ferris@rust-lang.org"),
];
static NODE_USER_EMAIL: &'static [Label] = &[
    Label::from_static_parts("node_name", "localhost"),
    Label::from_static_parts("user", "ferris"),
    Label::from_static_parts("user.email", "ferris@rust-lang.org"),
];
static SVC_NODE_USER_EMAIL: &'static [Label] = &[
    Label::from_static_parts("service", "login_service"),
    Label::from_static_parts("node_name", "localhost"),
    Label::from_static_parts("user", "ferris"),
    Label::from_static_parts("user.email", "ferris@rust-lang.org"),
];
static COMBINED_LABELS: &'static [Label] = &[
    Label::from_static_parts("shared_field", "inner"),
    Label::from_static_parts("inner_specific", "foo"),
    Label::from_static_parts("inner_specific_dynamic", "foo_dynamic"),
    Label::from_static_parts("shared_field", "outer"),
    Label::from_static_parts("outer_specific", "bar"),
    Label::from_static_parts("outer_specific_dynamic", "bar_dynamic"),
];
static SAME_CALLSITE_PATH_1: &'static [Label] = &[
    Label::from_static_parts("shared_field", "path1"),
    Label::from_static_parts("path1_specific", "foo"),
    Label::from_static_parts("path1_specific_dynamic", "foo_dynamic"),
];
static SAME_CALLSITE_PATH_2: &'static [Label] = &[
    Label::from_static_parts("shared_field", "path2"),
    Label::from_static_parts("path2_specific", "bar"),
    Label::from_static_parts("path2_specific_dynamic", "bar_dynamic"),
];

fn with_layer<F, F2, O>(layer: TracingContextLayer<F>, f: F2) -> O
where
    F: LabelFilter + Clone + 'static,
    F2: FnOnce() -> O,
{
    // Make sure we have the `DebuggingRecorder` installed, and that if there's already a per-thread registry on this
    // thread, that it's cleared before running `f`.
    let _ = RECORDER.get_or_init(|| {
        let recorder = DebuggingRecorder::per_thread();
        let recorder = layer.layer(recorder);

        metrics::set_boxed_recorder(Box::new(recorder)).expect("failed to install recorder");
    });

    Snapshotter::clear_current_thread();

    // Now creating a new `tracing` registry using the given context layer and set the dispatcher for this thread, and
    // run `f` within that context.
    let subscriber = Registry::default().with(MetricsLayer::new());
    let dispatch = Dispatch::new(subscriber);
    with_default(&dispatch, f)
}

#[test]
fn test_basic_functionality() {
    let snapshot = with_layer(TracingContextLayer::all(), || {
        let user = "ferris";
        let email = "ferris@rust-lang.org";
        let span = span!(Level::TRACE, "login", user, user.email = email);
        let _guard = span.enter();

        counter!("login_attempts", 1, "service" => "login_service");

        Snapshotter::current_thread_snapshot()
            .expect("must be registry after emitting metric")
            .into_vec()
    });

    assert_eq!(
        snapshot,
        vec![(
            CompositeKey::new(
                MetricKind::Counter,
                Key::from_static_parts(LOGIN_ATTEMPTS, SVC_USER_EMAIL)
            ),
            None,
            None,
            DebugValue::Counter(1),
        )]
    )
}

#[test]
fn test_macro_forms() {
    let snapshot = with_layer(TracingContextLayer::all(), || {
        let user = "ferris";
        let email = "ferris@rust-lang.org";
        let span = span!(Level::TRACE, "login", user, user.email = email);
        let _guard = span.enter();

        // No labels.
        counter!("login_attempts_no_labels", 1);
        // Static labels only.
        counter!("login_attempts_static_labels", 1, "service" => "login_service");
        // Dynamic labels only.
        let node_name = "localhost".to_string();
        counter!("login_attempts_dynamic_labels", 1, "node_name" => node_name.clone());
        // Static and dynamic.
        counter!("login_attempts_static_and_dynamic_labels", 1,
        "service" => "login_service", "node_name" => node_name.clone());

        Snapshotter::current_thread_snapshot()
            .expect("must be registry after emitting metric")
            .into_vec()
    });

    assert_eq!(
        snapshot,
        vec![
            (
                CompositeKey::new(
                    MetricKind::Counter,
                    Key::from_static_parts(LOGIN_ATTEMPTS_NONE, USER_EMAIL)
                ),
                None,
                None,
                DebugValue::Counter(1),
            ),
            (
                CompositeKey::new(
                    MetricKind::Counter,
                    Key::from_static_parts(LOGIN_ATTEMPTS_STATIC, SVC_USER_EMAIL),
                ),
                None,
                None,
                DebugValue::Counter(1),
            ),
            (
                CompositeKey::new(
                    MetricKind::Counter,
                    Key::from_static_parts(LOGIN_ATTEMPTS_DYNAMIC, NODE_USER_EMAIL),
                ),
                None,
                None,
                DebugValue::Counter(1),
            ),
            (
                CompositeKey::new(
                    MetricKind::Counter,
                    Key::from_static_parts(LOGIN_ATTEMPTS_BOTH, SVC_NODE_USER_EMAIL),
                ),
                None,
                None,
                DebugValue::Counter(1),
            ),
        ]
    )
}

#[test]
fn test_no_labels() {
    let snapshot = with_layer(TracingContextLayer::all(), || {
        let span = span!(Level::TRACE, "login");
        let _guard = span.enter();

        counter!("login_attempts", 1);

        Snapshotter::current_thread_snapshot()
            .expect("must be registry after emitting metric")
            .into_vec()
    });

    assert_eq!(
        snapshot,
        vec![(
            CompositeKey::new(MetricKind::Counter, Key::from_static_name(LOGIN_ATTEMPTS)),
            None,
            None,
            DebugValue::Counter(1),
        )]
    )
}

#[test]
fn test_multiple_paths_to_the_same_callsite() {
    let snapshot = with_layer(TracingContextLayer::all(), || {
        let shared_fn = || {
            counter!("my_counter", 1);
        };

        let path1 = || {
            let path1_specific_dynamic = "foo_dynamic";
            let span = span!(
                Level::TRACE,
                "path1",
                shared_field = "path1",
                path1_specific = "foo",
                path1_specific_dynamic,
            );
            let _guard = span.enter();
            shared_fn();
        };

        let path2 = || {
            let path2_specific_dynamic = "bar_dynamic";
            let span = span!(
                Level::TRACE,
                "path2",
                shared_field = "path2",
                path2_specific = "bar",
                path2_specific_dynamic,
            );
            let _guard = span.enter();
            shared_fn();
        };

        path1();
        path2();

        Snapshotter::current_thread_snapshot()
            .expect("must be registry after emitting metric")
            .into_vec()
    });

    assert_eq!(
        snapshot,
        vec![
            (
                CompositeKey::new(
                    MetricKind::Counter,
                    Key::from_static_parts(MY_COUNTER, SAME_CALLSITE_PATH_1),
                ),
                None,
                None,
                DebugValue::Counter(1),
            ),
            (
                CompositeKey::new(
                    MetricKind::Counter,
                    Key::from_static_parts(MY_COUNTER, SAME_CALLSITE_PATH_2),
                ),
                None,
                None,
                DebugValue::Counter(1),
            )
        ]
    )
}

#[test]
fn test_nested_spans() {
    let snapshot = with_layer(TracingContextLayer::all(), || {
        let inner = || {
            let inner_specific_dynamic = "foo_dynamic";
            let span = span!(
                Level::TRACE,
                "inner",
                shared_field = "inner",
                inner_specific = "foo",
                inner_specific_dynamic,
            );
            let _guard = span.enter();

            counter!("my_counter", 1);
        };

        let outer = || {
            let outer_specific_dynamic = "bar_dynamic";
            let span = span!(
                Level::TRACE,
                "outer",
                shared_field = "outer",
                outer_specific = "bar",
                outer_specific_dynamic,
            );
            let _guard = span.enter();
            inner();
        };

        outer();

        Snapshotter::current_thread_snapshot()
            .expect("must be registry after emitting metric")
            .into_vec()
    });

    assert_eq!(
        snapshot,
        vec![(
            CompositeKey::new(
                MetricKind::Counter,
                Key::from_static_parts(MY_COUNTER, COMBINED_LABELS)
            ),
            None,
            None,
            DebugValue::Counter(1),
        )]
    );
}

#[derive(Clone)]
struct OnlyUser;

impl LabelFilter for OnlyUser {
    fn should_include_label(&self, _name: &KeyName, label: &Label) -> bool {
        label.key() == "user"
    }
}

#[test]
fn test_label_filtering() {
    let snapshot = with_layer(TracingContextLayer::new(OnlyUser), || {
        let user = "ferris";
        let email = "ferris@rust-lang.org";
        let span = span!(Level::TRACE, "login", user, user.email_span = email);
        let _guard = span.enter();

        counter!("login_attempts", 1, "user.email" => "ferris@rust-lang.org");

        Snapshotter::current_thread_snapshot()
            .expect("must be registry after emitting metric")
            .into_vec()
    });

    assert_eq!(
        snapshot,
        vec![(
            CompositeKey::new(
                MetricKind::Counter,
                Key::from_static_parts(LOGIN_ATTEMPTS, EMAIL_USER)
            ),
            None,
            None,
            DebugValue::Counter(1),
        )]
    )
}

#[test]
fn test_label_allowlist() {
    let snapshot = with_layer(TracingContextLayer::only_allow(&["env", "service"]), || {
        let user = "ferris";
        let email = "ferris@rust-lang.org";
        let span = span!(
            Level::TRACE,
            "login",
            user,
            user.email_span = email,
            service = "login_service",
            env = "test"
        );
        let _guard = span.enter();

        counter!("login_attempts", 1);

        Snapshotter::current_thread_snapshot()
            .expect("must be registry after emitting metric")
            .into_vec()
    });

    assert_eq!(
        snapshot,
        vec![(
            CompositeKey::new(MetricKind::Counter, Key::from_static_parts(LOGIN_ATTEMPTS, SVC_ENV)),
            None,
            None,
            DebugValue::Counter(1),
        )]
    )
}

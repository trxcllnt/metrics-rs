//! Strongly-typed metadata associated with metrics.

use std::any::Any;

use dyn_clone::DynClone;

use crate::SharedString;

/// A metric attribute.
///
/// An attribute defines metadata associated with a metric. This can range from a single piece of
/// information, like the metric description, or more advanced information, all while being strongly typed.
///
/// This trait is not used directly in practice, but serves as a marker for a concrete type that
/// represents a specific attribute. In the future, methods may be added to this trait toi provide
/// additional functionality.
pub trait Attribute: Any + std::fmt::Debug + DynClone + Send + Sync {
    /// Returns a reference to the concrete attribute value if it is of type `T`, or `None` if it isn't.
    fn downcast_ref<T: 'static>(&self) -> Option<&T> where Self: Sized {
        (self as &dyn Any).downcast_ref::<T>()
    }
}

impl Attribute for Box<dyn Attribute> {}

dyn_clone::clone_trait_object!(Attribute);

#[derive(Clone, Debug)]
/// A metric description.
pub struct Description(SharedString);

impl Description {
    /// Converts the given description to an owned `String`.
    pub fn to_string(&self) -> String {
        self.0.to_string()
    }
}

impl<T> From<T> for Description
where
    T: Into<SharedString>,
{
    fn from(s: T) -> Self {
        Self(s.into())
    }
}

impl Attribute for Description {}

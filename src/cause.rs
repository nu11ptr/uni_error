// *** Enriched traits ***

use alloc::boxed::Box;
use core::{
    any::{Any, type_name, type_name_of_val},
    error::Error,
    fmt::{Debug, Display},
};

use crate::{
    UniError, UniKind,
    error::{DynError, UniErrorOps},
};

// FIXME: 'Any' shouldn't be necessary since Error has downcasting, but somehow we now depend on it.
/// Standard `Error` trait with `Any` to allow downcasting.
pub trait UniStdError: Any + Error + Send + Sync {
    /// Returns the concrete type name of the error.
    fn type_name(&self) -> &'static str {
        type_name::<Self>()
    }
}

impl<T> UniStdError for T where T: Error + Any + Send + Sync {}

/// Standard `Display` trait with `Any` to allow downcasting.
pub trait UniDisplay: Display + Debug + Any + Send + Sync {
    /// Returns the concrete type name of the error.
    fn type_name(&self) -> &'static str {
        // TODO: Find/replace 'UniError<()>' --> SimpleError, 'Box<dyn UniErrorTrait>' --> DynError
        // before returning type name
        type_name::<Self>()
    }
}

impl<T> UniDisplay for T where T: Display + Debug + Any + Send + Sync {}

// *** Downcast / FakeError ***

#[doc(hidden)]
#[derive(Debug, PartialEq)]
pub struct FakeError;

impl Display for FakeError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "FakeError")
    }
}

impl Error for FakeError {}

/// A reference to a downcasted error.
pub enum DowncastRef<'e, A: 'static = (), E: Error + 'static = FakeError> {
    /// A reference to a downcasted error for all non-`std::error::Error` types (includes `UniError` types)
    Any(&'e A),
    /// A reference to a downcasted error that implements `std::error::Error`.
    Error(&'e E),
}

// *** Cause ***

/// An error in the cause chain.
#[derive(Copy, Clone, Debug)]
pub enum Cause<'e> {
    /// A reference to any of the `UniError` types we wrapped.
    UniError(&'e DynError),
    /// A reference to a `std::error::Error` that we wrapped.
    UniStdError(&'e dyn UniStdError),
    /// A reference to a`std::error::Error` that was wrapped downstream (obtained via `source`).
    StdError(&'e (dyn Error + 'static)),
    /// A reference to a `std::fmt::Display` that we wrapped.
    UniDisplay(&'e dyn UniDisplay),
}

impl<'e> Cause<'e> {
    pub(crate) fn from_inner(inner: &'e CauseInner) -> Cause<'e> {
        match inner {
            CauseInner::UniError(err) => Cause::UniError(&err),
            CauseInner::UniStdError(err) => Cause::UniStdError(&**err),
            CauseInner::UniDisplay(err) => Cause::UniDisplay(&**err),
        }
    }

    fn any_downcast_ref<A: 'static>(err: &'e dyn Any) -> Option<&'e A> {
        err.downcast_ref::<A>()
    }

    fn error_downcast_ref<E: Error + 'static>(err: &'e (dyn Error + 'static)) -> Option<&'e E> {
        err.downcast_ref::<E>()
    }

    // Attempts to downcast this cause to a specific concrete type.
    pub fn downcast_ref<A: 'static, E: Error + 'static>(self) -> Option<DowncastRef<'e, A, E>> {
        match self {
            Cause::UniError(err) => Self::any_downcast_ref(&**err).map(DowncastRef::Any),
            Cause::UniStdError(err) => Self::error_downcast_ref(err).map(DowncastRef::Error),
            Cause::StdError(err) => Self::error_downcast_ref(err).map(DowncastRef::Error),
            Cause::UniDisplay(err) => Self::any_downcast_ref(err).map(DowncastRef::Any),
        }
    }

    // Return the actual type name of the cause.
    // NOTE: This will only give the trait object name for downstream errors before UniError wrapping was applied.
    pub fn type_name(self) -> &'static str {
        match self {
            Cause::UniError(err) => err.type_name(),
            Cause::UniStdError(err) => UniStdError::type_name(err),
            // This won't give us anything useful, but it's the best we can do to maintain consistency
            Cause::StdError(err) => type_name_of_val(err),
            Cause::UniDisplay(err) => err.type_name(),
        }
    }

    // Returns the next cause in the chain, if any.
    pub fn next(self) -> Option<Cause<'e>> {
        match self {
            Cause::UniError(err) => err.prev_cause().map(|cause| match cause {
                Cause::UniError(err) => Cause::UniError(err),
                Cause::UniStdError(err) => Cause::UniStdError(err),
                Cause::StdError(err) => Cause::StdError(err),
                Cause::UniDisplay(err) => Cause::UniDisplay(err),
            }),
            Cause::UniStdError(err) => err.source().map(|err| Cause::StdError(err)),
            Cause::StdError(err) => err.source().map(|err| Cause::StdError(err)),
            Cause::UniDisplay(_) => None,
        }
    }
}

impl<'e> Display for Cause<'e> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Cause::UniError(err) => <dyn UniErrorOps as Display>::fmt(&**err, f),
            Cause::UniStdError(err) => <dyn UniStdError as Display>::fmt(err, f),
            Cause::StdError(err) => <dyn Error as Display>::fmt(err, f),
            Cause::UniDisplay(err) => <dyn UniDisplay as Display>::fmt(err, f),
        }
    }
}

impl<'e> Error for Cause<'e> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Cause::UniError(err) => err.source(),
            Cause::UniStdError(err) => err.source(),
            Cause::StdError(err) => err.source(),
            Cause::UniDisplay(_) => None,
        }
    }
}

// *** Chain ***

/// An iterator over the cause chain of an error.
pub struct Chain<'e> {
    curr: Option<Cause<'e>>,
}

impl<'e> Chain<'e> {
    pub(crate) fn new(curr: Option<Cause<'e>>) -> Self {
        Self { curr }
    }
}

impl<'e> Iterator for Chain<'e> {
    type Item = Cause<'e>;

    fn next(&mut self) -> Option<Self::Item> {
        let curr = self.curr?;
        self.curr = curr.next();
        Some(curr)
    }
}

// *** CauseInner ***

#[derive(Debug)]
pub(crate) enum CauseInner {
    UniError(DynError),
    UniStdError(Box<dyn UniStdError + Send + Sync>),
    UniDisplay(Box<dyn UniDisplay + Send + Sync>),
}

impl CauseInner {
    pub fn from_display(cause: impl UniDisplay) -> CauseInner {
        CauseInner::UniDisplay(Box::new(cause))
    }

    pub fn from_error(cause: impl UniStdError) -> CauseInner {
        CauseInner::UniStdError(Box::new(cause))
    }

    pub fn from_uni_error<T: UniKind>(cause: UniError<T>) -> CauseInner {
        CauseInner::UniError(DynError::new(cause))
    }
}

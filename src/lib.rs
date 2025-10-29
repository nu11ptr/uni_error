#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

use core::{
    any::Any,
    error::Error,
    fmt::{Debug, Display},
    result::Result,
};
#[cfg(feature = "std")]
use std::borrow::Cow;

#[cfg(not(feature = "std"))]
use {alloc::borrow::Cow, alloc::boxed::Box};

// *** Type aliases ***

/// A result type that specifies a customkind.
pub type UniResult<T, U> = Result<T, UniError<U>>;

/// A result type that specifies no kind.
pub type SimpleResult<T> = Result<T, SimpleError>;

/// An error type that is used when there is no kind.
pub type SimpleError = UniError<()>;

/// An error type that is used as a cause when `UniKind` isn't `T`.
pub type UnknownUniError = UniError<Box<dyn UniKind>>;

// *** UniKind trait ***

/// A trait that specifies a custom error kind. Any specified to facilitate downcasting.
pub trait UniKind: Any + Send + Sync {
    /// Returns the default kind.
    fn default() -> Self
    where
        Self: Sized;

    /// Returns additional context for this specific kind, if any.
    fn context(&self) -> Option<&str> {
        None
    }

    /// Returns the code (typically for FFI) for this specific kind. Defaults to -1.
    fn code(&self) -> i32 {
        -1
    }
}

impl UniKind for () {
    fn default() -> Self {
        Default::default()
    }
}

impl UniKind for Box<dyn UniKind> {
    fn default() -> Self {
        unreachable!("Cannot create a default kind for a Box<dyn UniKind>");
    }

    fn context(&self) -> Option<&str> {
        self.as_ref().context()
    }
}

// *** Enriched traits ***

/// Standard `Error` trait with `Any` to allow downcasting.
pub trait UniStdError: Error + Any + Send + Sync {}

impl<T> UniStdError for T where T: Error + Any + Send + Sync {}

/// Standard `Display` trait with `Any` to allow downcasting.
pub trait UniDisplay: Display + Any + Send + Sync {}

impl<T> UniDisplay for T where T: Display + Any + Send + Sync {}

// *** Cause ***

/// An entry in the cause chain with varying degrees of richness, as available.
pub enum Cause<T> {
    SimpleError(SimpleError),
    UniError(UniError<T>),
    UnknownUniError(UnknownUniError),
    StdError(Box<dyn UniStdError>),
    Display(Box<dyn UniDisplay>),
}

impl<T: UniKind> Cause<T> {
    /// Attempts to obtain a reference to the specific kind when not `T`.
    pub fn unknown_kind<U: UniKind>(&self) -> Option<&U> {
        match self {
            Cause::UnknownUniError(err) => {
                let kind: &dyn Any = &**err.kind_ref();

                match kind.downcast_ref::<U>() {
                    Some(kind) => Some(kind),
                    None => None,
                }
            }
            _ => None,
        }
    }

    /// Attempts to downcast the cause to a specific `Error` type.
    pub fn as_error_type<U: UniStdError>(&self) -> Option<&U> {
        match self {
            Cause::StdError(err) => {
                let kind: &dyn Any = &**err;
                match kind.downcast_ref::<U>() {
                    Some(kind) => Some(kind),
                    None => None,
                }
            }
            _ => None,
        }
    }

    /// Attempts to downcast the cause to a specific `Display` type.
    pub fn as_display_type<U: UniDisplay>(&self) -> Option<&U> {
        match self {
            Cause::Display(err) => {
                let kind: &dyn Any = &**err;
                match kind.downcast_ref::<U>() {
                    Some(kind) => Some(kind),
                    None => None,
                }
            }
            _ => None,
        }
    }
}

impl<T: UniKind> Debug for Cause<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl<T: UniKind> Display for Cause<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Cause::SimpleError(err) => <SimpleError as Display>::fmt(err, f),
            Cause::UniError(err) => <UniError<T> as Display>::fmt(err, f),
            Cause::UnknownUniError(err) => <UnknownUniError as Display>::fmt(err, f),
            Cause::StdError(err) => <Box<dyn UniStdError> as Display>::fmt(err, f),
            Cause::Display(err) => <Box<dyn UniDisplay> as Display>::fmt(err, f),
        }
    }
}

impl<T: UniKind> Error for Cause<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Cause::SimpleError(err) => err.source(),
            Cause::UniError(err) => err.source(),
            Cause::UnknownUniError(err) => err.source(),
            Cause::StdError(err) => err.source(),
            Cause::Display(_) => None,
        }
    }
}

// *** UniError ***

struct UniErrorInner<T> {
    kind: T,
    context: Option<Cow<'static, str>>,
    cause: Option<Cause<T>>,
}

/// A custom error type that can be used to return an error with a custom error kind.
pub struct UniError<T> {
    inner: Box<UniErrorInner<T>>,
}

impl<T: UniKind> UniError<T> {
    fn new(kind: T, context: Option<Cow<'static, str>>, cause: Option<Cause<T>>) -> Self {
        Self {
            inner: Box::new(UniErrorInner {
                kind,
                context,
                cause,
            }),
        }
    }

    /// Creates a new `UniError` with a default kind, the provided context, and no cause.
    pub fn from_context(context: impl Into<Cow<'static, str>>) -> Self {
        Self::new(UniKind::default(), Some(context.into()), None)
    }

    /// Creates a new `UniError` with the provided kind and no context or cause.
    pub fn from_kind(kind: T) -> Self {
        Self::new(kind, None, None)
    }

    /// Creates a new `UniError` with the provided kind, the provided context, and no cause.
    pub fn from_kind_context(kind: T, context: impl Into<Cow<'static, str>>) -> Self {
        Self::new(kind, Some(context.into()), None)
    }

    fn build_kind_error_cause(cause: Box<dyn Any>, is_simple_error: bool) -> Cause<T> {
        if is_simple_error {
            Cause::SimpleError(
                *cause
                    .downcast::<SimpleError>()
                    .expect("cause is not a SimpleError"),
            )
        } else {
            Cause::UniError(
                *cause
                    .downcast::<UniError<T>>()
                    .expect("cause is not a UniError<T>"),
            )
        }
    }

    fn build_cause_display(cause: impl UniDisplay) -> Cause<T> {
        let is_simple_error = <dyn Any>::is::<SimpleError>(&cause);
        let is_kind_error = <dyn Any>::is::<UniError<T>>(&cause);

        if is_simple_error || is_kind_error {
            Self::build_kind_error_cause(Box::new(cause), is_simple_error)
        } else {
            Cause::Display(Box::new(cause))
        }
    }

    fn build_cause(cause: impl UniStdError) -> Cause<T> {
        let is_simple_error = <dyn Any>::is::<SimpleError>(&cause);
        let is_kind_error = <dyn Any>::is::<UniError<T>>(&cause);

        if is_simple_error || is_kind_error {
            Self::build_kind_error_cause(Box::new(cause), is_simple_error)
        } else {
            Cause::StdError(Box::new(cause))
        }
    }

    /// Returns a reference to the custom kind.
    pub fn kind_ref(&self) -> &T {
        &self.inner.kind
    }

    /// Returns the code (typically for FFI) for the custom kind.
    pub fn kind_code(&self) -> i32 {
        self.inner.kind.code()
    }

    /// Returns a reference to the first entry in the cause chain.
    pub fn cause(&self) -> Option<&Cause<T>> {
        self.inner.cause.as_ref()
    }
}

impl<T: Copy> UniError<T> {
    /// Returns a copy of the custom kind.
    pub fn kind(&self) -> T {
        self.inner.kind
    }
}

impl<T: UniKind> Debug for UniError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl<T: UniKind> Display for UniError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if let Some(context) = &self.inner.context {
            write!(f, "{}", context)?;
        }

        if let Some(context) = self.inner.kind.context() {
            if self.inner.context.is_some() {
                write!(f, ": ")?;
            }
            write!(f, "{}", context)?;
        }

        if let Some(cause) = &self.inner.cause {
            if self.inner.context.is_some() || self.inner.kind.context().is_some() {
                write!(f, ": ")?;
            }
            write!(f, "{}", cause)?;
        }

        Ok(())
    }
}

impl<T: UniKind> Error for UniError<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.cause() {
            Some(cause) => cause.source(),
            None => None,
        }
    }
}

// *** ErrorContext ***

/// A trait for wrapping an existing error with a additional context.
pub trait ErrorContext<T> {
    /// Wraps the existing error with the provided kind.
    fn with_kind(self, kind: T) -> UniError<T>;

    /// Wraps the existing error with the provided context.
    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniError<T>;

    /// Wraps the existing error with the provided kind and context.
    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T>;

    /// Wraps the existing error with no additional context.
    fn wrap(self) -> UniError<T>;
}

impl<T: UniKind, E: UniStdError> ErrorContext<T> for E {
    fn with_kind(self, kind: T) -> UniError<T> {
        UniError::new(kind, None, Some(UniError::build_cause(self)))
    }

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            UniKind::default(),
            Some(context.into()),
            Some(UniError::build_cause(self)),
        )
    }

    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(UniError::build_cause(self)),
        )
    }

    fn wrap(self) -> UniError<T> {
        UniError::new(UniKind::default(), None, Some(UniError::build_cause(self)))
    }
}

// *** ResultContext ***

/// A trait for wrapping an existing result error with a additional context.
pub trait ResultContext<T, U, E> {
    /// Wraps the existing result error with the provided kind.
    fn with_kind(self, kind: T) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided context.
    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided kind and context.
    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniResult<U, T>;

    /// Wraps the existing result error with no additional context.
    fn wrap(self) -> UniResult<U, T>;
}

impl<T: UniKind, U, E: UniStdError> ResultContext<T, U, E> for Result<U, E> {
    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.with_context(context))
    }

    fn with_kind(self, kind: T) -> UniResult<U, T> {
        self.map_err(|err| err.with_kind(kind))
    }

    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.with_kind_context(kind, context))
    }

    fn wrap(self) -> UniResult<U, T> {
        self.map_err(|err| err.wrap())
    }
}

// *** ErrorContextDisplay ***

/// A trait for wrapping an existing error with a additional context (for `Display` types).
pub trait ErrorContextDisplay<T> {
    /// Wraps the existing error with the provided kind (for `Display` types).
    fn with_kind_display(self, kind: T) -> UniError<T>;

    /// Wraps the existing error with the provided context (for `Display` types).
    fn with_context_display(self, context: impl Into<Cow<'static, str>>) -> UniError<T>;

    /// Wraps the existing error with the provided kind and context (for Display types).
    fn with_kind_context_display(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> UniError<T>;

    /// Wraps the existing error with no additional context (for `Display` types).
    fn wrap_display(self) -> UniError<T>;
}

impl<T: UniKind, E: UniDisplay> ErrorContextDisplay<T> for E {
    fn with_kind_display(self, kind: T) -> UniError<T> {
        UniError::new(kind, None, Some(UniError::build_cause_display(self)))
    }

    fn with_context_display(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            UniKind::default(),
            Some(context.into()),
            Some(UniError::build_cause_display(self)),
        )
    }

    fn with_kind_context_display(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> UniError<T> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(UniError::build_cause_display(self)),
        )
    }

    fn wrap_display(self) -> UniError<T> {
        UniError::new(
            UniKind::default(),
            None,
            Some(UniError::build_cause_display(self)),
        )
    }
}

// *** ResultContextDisplay ***

/// A trait for wrapping an existing result error with a additional context (for `Display` types).
pub trait ResultContextDisplay<T, U, E> {
    /// Wraps the existing result error with the provided kind (for `Display` types).
    fn with_kind_display(self, kind: T) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided context (for `Display` types).
    fn with_context_display(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided kind and context (for `Display` types).
    fn with_kind_context_display(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> UniResult<U, T>;

    /// Wraps the existing result error with no additional context (for `Display` types).
    fn wrap_display(self) -> UniResult<U, T>;
}

impl<T: UniKind, U, E: UniDisplay> ResultContextDisplay<T, U, E> for Result<U, E> {
    fn with_context_display(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.with_context_display(context))
    }

    fn with_kind_display(self, kind: T) -> UniResult<U, T> {
        self.map_err(|err| err.with_kind_display(kind))
    }

    fn with_kind_context_display(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> UniResult<U, T> {
        self.map_err(|err| err.with_kind_context_display(kind, context))
    }

    fn wrap_display(self) -> UniResult<U, T> {
        self.map_err(|err| err.wrap_display())
    }
}

// *** Tests ***

#[cfg(test)]
mod tests {
    #[cfg(not(feature = "std"))]
    extern crate alloc;

    #[cfg(not(feature = "std"))]
    use alloc::string::ToString;
    use core::cell::{BorrowMutError, RefCell};

    use super::*;

    fn propigate_error() -> UniResult<(), TestKind> {
        let test = RefCell::new(());
        let _borrow = test.borrow_mut();
        let _ = test.try_borrow_mut().with_context("test")?;
        Ok(())
    }

    #[derive(Debug, PartialEq, Eq)]
    enum TestKind {
        Test,
    }

    impl UniKind for TestKind {
        fn default() -> Self {
            TestKind::Test
        }
    }

    #[test]
    fn test_simple_error() {
        let err = SimpleError::from_context("test");
        assert_eq!(err.to_string(), "test");
        assert_eq!(err.kind(), ());
        assert!(err.cause().is_none());
    }

    #[test]
    fn test_kind_error() {
        let err: UniError<TestKind> = UniError::from_context("test");
        assert_eq!(err.to_string(), "test");
        assert_eq!(err.kind_ref(), &TestKind::Test);
        assert!(err.cause().is_none());
    }

    #[test]
    fn test_propigate_error() {
        let err = propigate_error().unwrap_err();
        assert_eq!(err.to_string(), "test: RefCell already borrowed");
        assert_eq!(err.kind_ref(), &TestKind::Test);
        assert!(matches!(err.cause(), Some(Cause::StdError(_))));
        assert!(
            err.cause()
                .unwrap()
                .as_error_type::<BorrowMutError>()
                .is_some()
        );
    }
}

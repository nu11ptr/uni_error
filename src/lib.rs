#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::{borrow::Cow, boxed::Box, sync::Arc};
use core::{
    any::{Any, type_name},
    error::Error,
    fmt::{Debug, Display},
    result::Result,
};
#[cfg(feature = "std")]
use std::{borrow::Cow, sync::Arc};

// *** Type aliases ***

/// A result type that specifies a customkind.
pub type UniResult<T, U> = Result<T, UniError<U>>;

/// A result type that specifies no kind.
pub type SimpleResult<T> = Result<T, SimpleError>;

/// A result type that specifies a trait object kind.
pub type DynResult<T> = Result<T, DynError>;

/// An error type that is used when there is no kind.
pub type SimpleError = UniError<()>;

/// A type that is used as a cause when `UniKind` isn't `T`.
pub type DynKind = Box<dyn UniKind>;

/// An error type that is used as a cause when `UniKind` isn't `T`.
pub type DynError = UniError<DynKind>;

// *** UniKind trait ***

/// A trait that specifies a custom error kind. Any specified to facilitate downcasting.
pub trait UniKind: Debug + Any + Send + Sync {
    /// Returns the default kind.
    fn default() -> Self
    where
        Self: Sized;

    // The string value of the kind, if any. This is useful for programmatic evaluation
    // when the type is boxed in the error chain and the type is not known.
    fn str_value(&self) -> &str {
        ""
    }

    /// Returns additional context for this specific kind, if any.
    fn context(&self) -> Option<&str> {
        None
    }

    /// Returns the code (typically for FFI) for this specific kind. Defaults to -1.
    fn code(&self) -> i32 {
        -1
    }
}

impl dyn UniKind {
    /// The string name of the type implementing this trait.
    fn type_name(&self) -> &str {
        type_name::<Self>()
    }
}

impl UniKind for () {
    fn default() -> Self {
        Default::default()
    }
}

impl UniKind for DynKind {
    fn default() -> Self {
        unreachable!("Cannot create a default kind for a Box<dyn UniKind>");
    }

    fn str_value(&self) -> &str {
        self.as_ref().str_value()
    }

    fn context(&self) -> Option<&str> {
        self.as_ref().context()
    }

    fn code(&self) -> i32 {
        self.as_ref().code()
    }
}

// *** Enriched traits ***

// TODO: Error already has downcasting - Any shouldn't be necessary
/// Standard `Error` trait with `Any` to allow downcasting.
pub trait UniStdError: Error + Any + Send + Sync {}

impl dyn UniStdError {
    pub fn type_name(&self) -> &str {
        type_name::<Self>()
    }
}

impl<T> UniStdError for T where T: Error + Any + Send + Sync {}

/// Standard `Display` trait with `Any` to allow downcasting.
pub trait UniDisplay: Display + Debug + Any + Send + Sync {}

impl dyn UniDisplay {
    pub fn type_name(&self) -> &str {
        type_name::<Self>()
    }
}

impl<T> UniDisplay for T where T: Display + Debug + Any + Send + Sync {}

// *** Cause ***

impl<'e, T> Copy for Cause<'e, T> {}

impl<'e, T> Clone for Cause<'e, T> {
    fn clone(&self) -> Self {
        *self
    }
}

/// The cause of an error.
pub enum Cause<'e, T> {
    SimpleError(&'e SimpleError),
    UniError(&'e UniError<T>),
    DynError(&'e DynError),
    UniStdError(&'e dyn UniStdError),
    StdError(&'e (dyn Error + 'static)),
    UniDisplay(&'e dyn UniDisplay),
}

impl<'e, T: UniKind> Cause<'e, T> {
    fn from_inner(inner: &'e CauseInner<T>) -> Cause<'e, T> {
        match inner {
            CauseInner::SimpleError(err) => Cause::SimpleError(err),
            CauseInner::UniError(err) => Cause::UniError(err),
            CauseInner::DynError(err) => Cause::DynError(err),
            CauseInner::UniStdError(err) => Cause::UniStdError(&**err),
            CauseInner::UniDisplay(err) => Cause::UniDisplay(err),
        }
    }

    /// Attempts to obtain a reference to the specific kind when not `T`.
    pub fn dyn_kind<U: UniKind>(&self) -> Option<&U> {
        match self {
            Cause::DynError(err) => {
                let kind: &dyn Any = &**err.kind_ref();
                kind.downcast_ref::<U>()
            }
            _ => None,
        }
    }

    /// Attempts to downcast this cause to a specific concrete type.
    pub fn as_type_ref<U: UniStdError>(&self) -> Option<&U> {
        match self {
            Cause::UniStdError(err) => Self::error_downcast_ref(*err),
            Cause::StdError(err) => err.downcast_ref(),
            Cause::UniDisplay(err) => {
                let err: &dyn Any = &**err;
                err.downcast_ref::<U>()
            }
            _ => None,
        }
    }

    fn error_downcast_ref<U: UniStdError>(err: &'e (dyn Error + 'static)) -> Option<&'e U> {
        err.downcast_ref::<U>()
    }

    fn uni_std_error_as_type(err: &'e dyn UniStdError) -> Cause<'e, T> {
        if let Some(err) = Self::error_downcast_ref(err) {
            Cause::SimpleError(err)
        } else if let Some(err) = Self::error_downcast_ref(err) {
            Cause::UniError(err)
        } else if let Some(err) = Self::error_downcast_ref(err) {
            Cause::DynError(err)
        } else {
            Cause::UniStdError(err)
        }
    }

    fn std_error_as_type(err: &'e (dyn Error + 'static)) -> Cause<'e, T> {
        if let Some(err) = err.downcast_ref() {
            Cause::SimpleError(err)
        } else if let Some(err) = err.downcast_ref() {
            Cause::UniError(err)
        } else if let Some(err) = err.downcast_ref() {
            Cause::DynError(err)
        } else {
            Cause::StdError(err)
        }
    }

    // Returns the next cause in the chain, if any.
    pub fn next(self) -> Option<Cause<'e, T>> {
        match self {
            Cause::SimpleError(err) => err.prev_cause().map(|cause| match cause {
                Cause::SimpleError(err) => Cause::SimpleError(err),
                Cause::UniError(err) => Cause::SimpleError(err),
                Cause::DynError(err) => Cause::DynError(err),
                Cause::UniStdError(err) => Self::uni_std_error_as_type(err),
                Cause::StdError(err) => Self::std_error_as_type(err),
                Cause::UniDisplay(err) => Cause::UniDisplay(err),
            }),
            Cause::UniError(err) => err.prev_cause().map(|cause| match cause {
                Cause::SimpleError(err) => Cause::SimpleError(err),
                Cause::UniError(err) => Cause::UniError(err),
                Cause::DynError(err) => Cause::DynError(err),
                Cause::UniStdError(err) => Self::uni_std_error_as_type(err),
                Cause::StdError(err) => Self::std_error_as_type(err),
                Cause::UniDisplay(err) => Cause::UniDisplay(err),
            }),
            Cause::DynError(err) => err.prev_cause().map(|cause| match cause {
                Cause::SimpleError(err) => Cause::SimpleError(err),
                Cause::UniError(err) => Cause::DynError(err),
                Cause::DynError(err) => Cause::DynError(err),
                Cause::UniStdError(err) => Self::uni_std_error_as_type(err),
                Cause::StdError(err) => Self::std_error_as_type(err),
                Cause::UniDisplay(err) => Cause::UniDisplay(err),
            }),
            Cause::UniStdError(err) => err.source().map(|err| Self::std_error_as_type(err)),
            Cause::StdError(err) => err.source().map(|err| Self::std_error_as_type(err)),
            Cause::UniDisplay(_) => None,
        }
    }
}

impl<'e, T: UniKind> Debug for Cause<'e, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Cause::SimpleError(err) => <SimpleError as Debug>::fmt(err, f),
            Cause::UniError(err) => <UniError<T> as Debug>::fmt(err, f),
            Cause::DynError(err) => <DynError as Debug>::fmt(err, f),
            Cause::UniStdError(err) => <dyn UniStdError as Debug>::fmt(err, f),
            Cause::StdError(err) => <dyn Error as Debug>::fmt(err, f),
            Cause::UniDisplay(err) => <dyn UniDisplay as Debug>::fmt(err, f),
        }
    }
}

impl<'e, T: UniKind> Display for Cause<'e, T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Cause::SimpleError(err) => <SimpleError as Display>::fmt(err, f),
            Cause::UniError(err) => <UniError<T> as Display>::fmt(err, f),
            Cause::DynError(err) => <DynError as Display>::fmt(err, f),
            Cause::UniStdError(err) => <dyn UniStdError as Display>::fmt(err, f),
            Cause::StdError(err) => <dyn Error as Display>::fmt(err, f),
            Cause::UniDisplay(err) => <dyn UniDisplay as Display>::fmt(err, f),
        }
    }
}

impl<'e, T: UniKind> Error for Cause<'e, T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Cause::SimpleError(err) => err.source(),
            Cause::UniError(err) => err.source(),
            Cause::DynError(err) => err.source(),
            Cause::UniStdError(err) => err.source(),
            Cause::StdError(err) => err.source(),
            Cause::UniDisplay(_) => None,
        }
    }
}

// *** Chain ***

/// An iterator over the cause chain of an error.
pub struct Chain<'e, T: UniKind> {
    curr: Option<Cause<'e, T>>,
}

impl<'e, T: UniKind> Iterator for Chain<'e, T> {
    type Item = Cause<'e, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let curr = self.curr?;
        self.curr = curr.next();
        Some(curr)
    }
}

// *** UniError ***

#[derive(Debug)]
enum CauseInner<T> {
    SimpleError(SimpleError),
    UniError(UniError<T>),
    #[allow(dead_code)]
    DynError(DynError),
    UniStdError(Box<dyn UniStdError>),
    UniDisplay(Box<dyn UniDisplay>),
}

#[derive(Debug)]
struct UniErrorInner<T> {
    kind: T,
    context: Option<Cow<'static, str>>,
    cause: Option<CauseInner<T>>,
}

/// A custom error type that can be used to return an error with a custom error kind.
#[derive(Clone, Debug)]
pub struct UniError<T> {
    inner: Arc<UniErrorInner<T>>,
}

impl<T: UniKind> UniError<T> {
    fn new(kind: T, context: Option<Cow<'static, str>>, cause: Option<CauseInner<T>>) -> Self {
        Self {
            inner: Arc::new(UniErrorInner {
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

    fn build_kind_error_cause(cause: Box<dyn Any>, is_simple_error: bool) -> CauseInner<T> {
        if is_simple_error {
            CauseInner::SimpleError(
                *cause
                    .downcast::<SimpleError>()
                    .expect("cause is not a SimpleError"),
            )
        } else {
            CauseInner::UniError(
                *cause
                    .downcast::<UniError<T>>()
                    .expect("cause is not a UniError<T>"),
            )
        }
    }

    fn build_cause_display(cause: impl UniDisplay) -> CauseInner<T> {
        let is_simple_error = <dyn Any>::is::<SimpleError>(&cause);
        let is_kind_error = <dyn Any>::is::<UniError<T>>(&cause);

        if is_simple_error || is_kind_error {
            Self::build_kind_error_cause(Box::new(cause), is_simple_error)
        } else {
            CauseInner::UniDisplay(Box::new(cause))
        }
    }

    fn build_cause(cause: impl UniStdError) -> CauseInner<T> {
        let is_simple_error = <dyn Any>::is::<SimpleError>(&cause);
        let is_kind_error = <dyn Any>::is::<UniError<T>>(&cause);

        if is_simple_error || is_kind_error {
            Self::build_kind_error_cause(Box::new(cause), is_simple_error)
        } else {
            CauseInner::UniStdError(Box::new(cause))
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

    pub fn kind_str_value(&self) -> &str {
        self.inner.kind.str_value()
    }

    /// Returns a reference to the first entry in the cause chain.
    pub fn prev_cause<'e>(&'e self) -> Option<Cause<'e, T>> {
        self.inner
            .cause
            .as_ref()
            .map(|inner| Cause::from_inner(inner))
    }

    pub fn chain(&self) -> Chain<'_, T> {
        Chain {
            curr: self.prev_cause(),
        }
    }

    // TODO: Remove Option and make 'self' a possible candidate
    /// Returns the root cause of this error. If `None` is returned then this error is the root cause.
    pub fn root_cause(&self) -> Option<Cause<'_, T>> {
        let mut chain = self.chain();
        let mut root = chain.next();

        while let Some(next) = chain.next() {
            root = Some(next);
        }
        root
    }
}

impl<T: Copy> UniError<T> {
    /// Returns a copy of the custom kind.
    pub fn kind(&self) -> T {
        self.inner.kind
    }
}

impl UniError<DynKind> {
    pub fn kind_type_name(&self) -> &str {
        self.inner.kind.type_name()
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

        if let Some(cause) = &self.prev_cause() {
            if self.inner.context.is_some() || self.inner.kind.context().is_some() {
                write!(f, ": ")?;
            }
            write!(f, "{}", cause)?;
        }

        Ok(())
    }
}

// impl<T: UniKind, E: UniStdError> From<E> for UniError<T> {
//     fn from(err: E) -> Self {
//         UniError::new(UniKind::default(), None, Some(UniError::build_cause(err)))
//     }
// }

impl<T: UniKind> Error for UniError<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.prev_cause() {
            Some(Cause::SimpleError(err)) => Some(err),
            Some(Cause::UniError(err)) => Some(err),
            Some(Cause::DynError(err)) => Some(err),
            Some(Cause::UniStdError(err)) => Some(err),
            Some(Cause::StdError(err)) => Some(err),
            Some(Cause::UniDisplay(_)) | None => None,
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
        assert!(err.prev_cause().is_none());
    }

    #[test]
    fn test_kind_error() {
        let err: UniError<TestKind> = UniError::from_context("test");
        assert_eq!(err.to_string(), "test");
        assert_eq!(err.kind_ref(), &TestKind::Test);
        assert!(err.prev_cause().is_none());
    }

    #[test]
    fn test_propigate_error() {
        let err = propigate_error().unwrap_err();
        assert_eq!(err.to_string(), "test: RefCell already borrowed");
        assert_eq!(err.kind_ref(), &TestKind::Test);
        assert!(matches!(err.prev_cause(), Some(Cause::UniStdError(_))));
        assert!(
            err.prev_cause()
                .unwrap()
                .as_type_ref::<BorrowMutError>()
                .is_some()
        );
    }
}

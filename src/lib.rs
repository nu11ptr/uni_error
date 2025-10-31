#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::{borrow::Cow, boxed::Box, sync::Arc};
use core::{
    any::{Any, TypeId, type_name},
    error::Error,
    fmt::{Debug, Display},
    ops::Deref,
    result::Result,
};
#[cfg(feature = "std")]
use std::{borrow::Cow, sync::Arc};

// #[doc = include_str!("../README.md")]
// mod readme_tests {}

// *** Type aliases ***

/// A result type that specifies a customkind.
pub type UniResult<T, U> = Result<T, UniError<U>>;

/// A result type that specifies no kind.
pub type SimpleResult<T> = Result<T, SimpleError>;

/// A result type that specifies a trait object kind.
pub type DynResult<T> = Result<T, DynError>;

/// An error type that is used when there is no kind.
pub type SimpleError = UniError<()>;

/// An error type that is used as a cause when `UniKind` isn't `T`.
pub type DynError = Arc<dyn UniErrorTrait + Send + Sync>;

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
    pub fn type_name(&self) -> &str {
        type_name::<Self>()
    }

    pub fn is_same_type<U: UniKind>(&self) -> bool {
        self.type_id() == TypeId::of::<U>()
    }
}

impl UniKind for () {
    fn default() -> Self {
        Default::default()
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

impl<'e> Copy for Cause<'e> {}

impl<'e> Clone for Cause<'e> {
    fn clone(&self) -> Self {
        *self
    }
}

/// The cause of an error.
#[derive(Debug)]
pub enum Cause<'e> {
    UniError(&'e DynError),
    UniStdError(&'e dyn UniStdError),
    StdError(&'e (dyn Error + 'static)),
    UniDisplay(&'e dyn UniDisplay),
}

impl<'e> Cause<'e> {
    fn from_inner(inner: &'e CauseInner) -> Cause<'e> {
        match inner {
            CauseInner::UniError(err) => Cause::UniError(err),
            CauseInner::UniStdError(err) => Cause::UniStdError(&**err),
            CauseInner::UniDisplay(err) => Cause::UniDisplay(err),
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

    // Returns the next cause in the chain, if any.
    pub fn next(self) -> Option<Cause<'e>> {
        match self {
            Cause::UniError(err) => err.prev_cause().map(|cause| match cause {
                Cause::UniError(err) => Cause::UniError(err),
                Cause::UniStdError(err) => Cause::UniStdError(err),
                Cause::StdError(err) => Cause::StdError(err),
                Cause::UniDisplay(err) => Cause::UniDisplay(err),
            }),
            Cause::UniStdError(err) => Some(Cause::UniStdError(err)),
            Cause::StdError(err) => Some(Cause::StdError(err)),
            Cause::UniDisplay(_) => None,
        }
    }
}

impl<'e> Display for Cause<'e> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match *self {
            Cause::UniError(err) => <DynError as Display>::fmt(err, f),
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
enum CauseInner {
    UniError(DynError),
    UniStdError(Box<dyn UniStdError + Send + Sync>),
    UniDisplay(Box<dyn UniDisplay + Send + Sync>),
}

// *** UniErrorInner ***

#[derive(Debug)]
struct UniErrorInner<T> {
    kind: T,
    context: Option<Cow<'static, str>>,
    cause: Option<CauseInner>,
}

impl<T: UniKind> UniErrorInner<T> {
    pub fn prev_cause<'e>(&'e self) -> Option<Cause<'e>> {
        self.cause.as_ref().map(|inner| Cause::from_inner(inner))
    }
}

impl<T: UniKind> Display for UniErrorInner<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        if let Some(context) = &self.context {
            write!(f, "{}", context)?;
        }

        if let Some(context) = self.kind.context() {
            if self.context.is_some() {
                write!(f, ": ")?;
            }
            write!(f, "{}", context)?;
        }

        if let Some(cause) = &self.prev_cause() {
            if self.context.is_some() || self.kind.context().is_some() {
                write!(f, ": ")?;
            }
            write!(f, "{}", cause)?;
        }

        Ok(())
    }
}

impl<T: UniKind> Error for UniErrorInner<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.prev_cause() {
            Some(Cause::UniError(err)) => Some(&***err),
            Some(Cause::UniStdError(err)) => Some(err),
            Some(Cause::StdError(err)) => Some(err),
            Some(Cause::UniDisplay(_)) | None => None,
        }
    }
}

// *** UniError ***

/// A custom error type that can be used to return an error with a custom error kind.
#[derive(Clone, Debug)]
pub struct UniError<T> {
    inner: Arc<UniErrorInner<T>>,
}

impl<T: UniKind> UniError<T> {
    fn new(kind: T, context: Option<Cow<'static, str>>, cause: Option<CauseInner>) -> Self {
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

    fn build_uni_error_cause(cause: Box<dyn Any>) -> CauseInner {
        let dyn_error: DynError = if cause.is::<SimpleError>() {
            Arc::new(
                *cause
                    .downcast::<SimpleError>()
                    .expect("cause is not a SimpleError"),
            )
        } else if cause.is::<DynError>() {
            *cause
                .downcast::<DynError>()
                .expect("cause is not a DynError")
        } else if cause.is::<UniError<T>>() {
            Arc::new(
                *cause
                    .downcast::<UniError<T>>()
                    .expect("cause is not a UniError<T>"),
            )
        } else {
            unreachable!("cause is not a SimpleError, DynError, or UniError<T>");
        };

        CauseInner::UniError(dyn_error)
    }

    fn build_cause_display(cause: impl UniDisplay) -> CauseInner {
        let is_uni_error = <dyn Any>::is::<UniError<T>>(&cause)
            || <dyn Any>::is::<DynError>(&cause)
            || <dyn Any>::is::<SimpleError>(&cause);

        // We implement Display, so this might be a UniError
        if is_uni_error {
            Self::build_uni_error_cause(Box::new(cause))
        } else {
            CauseInner::UniDisplay(Box::new(cause))
        }
    }

    fn build_cause_error(cause: impl UniStdError) -> CauseInner {
        CauseInner::UniStdError(Box::new(cause))
    }

    fn build_cause<U: UniKind>(cause: UniError<U>) -> CauseInner {
        CauseInner::UniError(Arc::new(cause))
    }

    /// Returns a reference to the custom kind.
    pub fn kind_ref(&self) -> &T {
        &self.inner.kind
    }
}

impl<T: Copy> UniError<T> {
    /// Returns a copy of the custom kind.
    pub fn kind(&self) -> T {
        self.inner.kind
    }
}

pub trait UniErrorTrait:
    Debug + Display + Any + Deref<Target = dyn Error + Send + Sync + 'static> + Send + Sync
{
    /// Returns the code (typically for FFI) for the custom kind.
    fn kind_code(&self) -> i32;

    fn kind_str_value(&self) -> &str;

    fn kind_obj_ref(&self) -> &dyn UniKind;

    /// Returns a reference to the first entry in the cause chain.
    fn prev_cause<'e>(&'e self) -> Option<Cause<'e>>;

    fn chain(&self) -> Chain<'_>;

    // TODO: Remove Option and make 'self' a possible candidate
    /// Returns the root cause of this error. If `None` is returned then this error is the root cause.
    fn root_cause(&self) -> Option<Cause<'_>>;
}

impl<T: UniKind> UniErrorTrait for UniError<T> {
    fn kind_code(&self) -> i32 {
        self.kind_ref().code()
    }

    fn kind_str_value(&self) -> &str {
        self.kind_ref().str_value()
    }

    fn kind_obj_ref(&self) -> &dyn UniKind {
        self.kind_ref()
    }

    fn prev_cause<'e>(&'e self) -> Option<Cause<'e>> {
        self.inner.prev_cause()
    }

    fn chain(&self) -> Chain<'_> {
        Chain {
            curr: self.prev_cause(),
        }
    }

    fn root_cause(&self) -> Option<Cause<'_>> {
        let mut chain = self.chain();
        let mut root = chain.next();

        while let Some(next) = chain.next() {
            root = Some(next);
        }
        root
    }
}

impl dyn UniErrorTrait {
    pub fn kind_type_name(&self) -> &str {
        self.kind_obj_ref().type_name()
    }
}

impl<T: UniKind> Display for UniError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <UniErrorInner<T> as Display>::fmt(&self.inner, f)
    }
}

impl<T: UniKind> Deref for UniError<T> {
    type Target = dyn Error + Sync + Send + 'static;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: UniKind> AsRef<dyn Error + Sync + Send> for UniError<T> {
    fn as_ref(&self) -> &(dyn Error + Sync + Send + 'static) {
        &**self
    }
}

impl<T: UniKind, E: UniStdError> From<E> for UniError<T> {
    fn from(err: E) -> Self {
        ErrorContext::wrap(err)
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
        UniError::new(kind, None, Some(UniError::<T>::build_cause_error(self)))
    }

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            UniKind::default(),
            Some(context.into()),
            Some(UniError::<T>::build_cause_error(self)),
        )
    }

    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(UniError::<T>::build_cause_error(self)),
        )
    }

    fn wrap(self) -> UniError<T> {
        UniError::new(
            UniKind::default(),
            None,
            Some(UniError::<T>::build_cause_error(self)),
        )
    }
}

impl<T: UniKind, U: UniKind> ErrorContext<T> for UniError<U> {
    fn with_kind(self, kind: T) -> UniError<T> {
        UniError::new(kind, None, Some(UniError::<T>::build_cause(self)))
    }

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            UniKind::default(),
            Some(context.into()),
            Some(UniError::<T>::build_cause(self)),
        )
    }

    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(UniError::<T>::build_cause(self)),
        )
    }

    fn wrap(self) -> UniError<T> {
        UniError::new(
            UniKind::default(),
            None,
            Some(UniError::<T>::build_cause(self)),
        )
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
    fn with_kind(self, kind: T) -> UniResult<U, T> {
        self.map_err(|err| err.with_kind(kind))
    }

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.with_context(context))
    }

    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.with_kind_context(kind, context))
    }

    fn wrap(self) -> UniResult<U, T> {
        self.map_err(|err| err.wrap())
    }
}

impl<T: UniKind, U: UniKind, V> ResultContext<U, V, T> for UniResult<V, T> {
    fn with_kind(self, kind: U) -> UniResult<V, U> {
        self.map_err(|err| err.with_kind(kind))
    }

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<V, U> {
        self.map_err(|err| err.with_context(context))
    }

    fn with_kind_context(self, kind: U, context: impl Into<Cow<'static, str>>) -> UniResult<V, U> {
        self.map_err(|err| err.with_kind_context(kind, context))
    }

    fn wrap(self) -> UniResult<V, U> {
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
        UniError::new(kind, None, Some(UniError::<T>::build_cause_display(self)))
    }

    fn with_context_display(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            UniKind::default(),
            Some(context.into()),
            Some(UniError::<T>::build_cause_display(self)),
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
            Some(UniError::<T>::build_cause_display(self)),
        )
    }

    fn wrap_display(self) -> UniError<T> {
        UniError::new(
            UniKind::default(),
            None,
            Some(UniError::<T>::build_cause_display(self)),
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

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(not(feature = "std"))]
use alloc::{borrow::Cow, boxed::Box, sync::Arc};
use core::{
    any::{Any, TypeId, type_name, type_name_of_val},
    error::Error,
    fmt::{Debug, Display},
    ops::Deref,
    result::Result,
};
#[cfg(feature = "std")]
use std::{borrow::Cow, sync::Arc};

#[doc = include_str!("../README.md")]
mod readme_tests {}

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
pub type DynError = Box<dyn UniErrorOps + Send + Sync>;

// *** UniKind trait ***

/// A trait that specifies a custom error kind. Any specified to facilitate downcasting.
pub trait UniKind: Debug + Any + Send + Sync {
    // The string value of the kind, if any. This is useful for programmatic evaluation
    // when the type is boxed in the error chain and the type is not known. Defaults to `""`.
    fn kind_value(&self) -> &str {
        ""
    }

    /// Returns additional context for this specific kind, if any. Defaults to `None`.
    fn kind_context(&self) -> Option<&str> {
        None
    }

    /// Returns the code (typically for FFI) for this specific kind. Defaults to -1.
    fn kind_code(&self) -> i32 {
        -1
    }

    // Return a trait object reference to the kind.
    fn kind_obj_ref(&self) -> &dyn UniKind
    where
        Self: Sized,
    {
        self
    }
}

impl UniKind for () {}

// *** Enriched traits ***

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

// TODO: Are there benefits to removing the Option and adding a None variant?
/// A reference to a downcasted error.
pub enum DowncastRef<'e, A: 'static = (), E: Error + 'static = FakeError> {
    /// A reference to a downcasted error for all non-`std::error::Error` types (includes `UniError` types)
    Any(Option<&'e A>),
    /// A reference to a downcasted error that implements `std::error::Error`.
    Error(Option<&'e E>),
}

// *** Cause ***

/// An error in the cause chain.
#[derive(Copy, Clone, Debug)]
pub enum Cause<'e> {
    /// A reference to any of the `UniError` types we wrapped.
    UniError(&'e dyn UniErrorOps),
    /// A reference to a `std::error::Error` that we wrapped.
    UniStdError(&'e dyn UniStdError),
    /// A reference to a`std::error::Error` that was wrapped downstream (obtained via `source`).
    StdError(&'e (dyn Error + 'static)),
    /// A reference to a `std::fmt::Display` that we wrapped.
    UniDisplay(&'e dyn UniDisplay),
}

impl<'e> Cause<'e> {
    fn from_inner(inner: &'e CauseInner) -> Cause<'e> {
        match inner {
            CauseInner::UniError(err) => Cause::UniError(&**err),
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
    pub fn downcast_ref<A: 'static, E: Error + 'static>(self) -> DowncastRef<'e, A, E> {
        match self {
            Cause::UniError(err) => DowncastRef::Any(Self::any_downcast_ref(err)),
            Cause::UniStdError(err) => DowncastRef::Error(Self::error_downcast_ref(err)),
            Cause::StdError(err) => DowncastRef::Error(Self::error_downcast_ref(err)),
            Cause::UniDisplay(err) => DowncastRef::Any(Self::any_downcast_ref(err)),
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
            Cause::UniError(err) => <dyn UniErrorOps as Display>::fmt(err, f),
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

        if let Some(context) = self.kind.kind_context() {
            if self.context.is_some() {
                write!(f, ": ")?;
            }
            write!(f, "{}", context)?;
        }

        if let Some(cause) = &self.prev_cause() {
            if self.context.is_some() || self.kind.kind_context().is_some() {
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
            Some(Cause::UniError(err)) => Some(&**err),
            Some(Cause::UniStdError(err)) => Some(err),
            Some(Cause::StdError(err)) => Some(err),
            Some(Cause::UniDisplay(_)) | None => None,
        }
    }
}

// *** UniError ***

/// A custom error type that can be used to return an error with a custom error kind.
#[derive(Debug)]
pub struct UniError<T> {
    inner: Arc<UniErrorInner<T>>,
}

impl<T: UniKind + Default> UniError<T> {
    /// Creates a new `UniError` with a default kind, the provided context, and no cause.
    pub fn from_context(context: impl Into<Cow<'static, str>>) -> Self {
        Self::new(Default::default(), Some(context.into()), None)
    }
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
            cause
                .downcast::<SimpleError>()
                .expect("cause is not a SimpleError")
        } else if cause.is::<DynError>() {
            *cause
                .downcast::<DynError>()
                .expect("cause is not a DynError")
        } else if cause.is::<UniError<T>>() {
            cause
                .downcast::<UniError<T>>()
                .expect("cause is not a UniError<T>")
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
        CauseInner::UniError(Box::new(cause))
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

/// A trait that specifies the operations that can be performed on a `UniError`.
pub trait UniErrorOps:
    UniKind + UniDisplay + Deref<Target = dyn Error + Send + Sync + 'static>
{
    /// Returns a reference to the first entry in the cause chain.
    fn prev_cause<'e>(&'e self) -> Option<Cause<'e>>;

    /// Returns an iterator over the cause chain.
    fn chain(&self) -> Chain<'_>;

    // TODO: Remove Option and make 'self' a possible candidate
    /// Returns the root cause of this error. If `None` is returned then this error is the root cause.
    fn root_cause(&self) -> Option<Cause<'_>>;
}

impl dyn UniErrorOps + Send + Sync {
    // TODO: I think this requires making DynError a newtype wrapper
    // as we can't create an impl Box<dyn Any> block
    /// Attempts to downcast a `DynError` to a `UniError<T>`.
    // pub fn downcast<T: UniKind>(self) -> Option<UniError<T>> {
    //     let err: Box<dyn Any> = self;
    //     err.downcast().ok().map(|err| *err)
    // }

    /// Attempts to downcast a `DynError` to a reference to a `UniError<T>`.
    pub fn downcast_ref<T: UniKind>(&self) -> Option<&UniError<T>> {
        let err: &dyn Any = self;
        err.downcast_ref()
    }
}

impl<T: UniKind> UniErrorOps for UniError<T> {
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

impl<T: UniKind> UniKind for UniError<T> {}

impl<T: UniKind> Display for UniError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <UniErrorInner<T> as Display>::fmt(&self.inner, f)
    }
}

// Manually implement as derive requires T: Clone
impl<T: UniKind> Clone for UniError<T> {
    fn clone(&self) -> Self {
        Self {
            inner: Arc::clone(&self.inner),
        }
    }
}

impl<T: PartialEq + 'static> PartialEq for UniError<T> {
    fn eq(&self, other: &Self) -> bool {
        // Kind values must be equal at minimum
        if self.inner.kind == other.inner.kind {
            // If the kind is `()`, then the context must be equal, otherwise
            // kind equality alone is sufficient
            if self.type_id() == TypeId::of::<()>() {
                self.inner.context == other.inner.context
            } else {
                true
            }
        } else {
            false
        }
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

impl<T: UniKind + Default, E: UniStdError> From<E> for UniError<T> {
    fn from(err: E) -> Self {
        ErrorContext::wrap(err)
    }
}

impl<E: UniErrorOps> From<E> for DynError {
    fn from(err: E) -> Self {
        Box::new(err)
    }
}

/// A wrapper for a `UniError` that implements the `Error` trait. Useful for
/// converting a `UniError` to a `Box<dyn Error + Send + Sync>` (and back via
/// downcasting).
#[derive(Debug)]
pub struct StdErrorWrapper<T>(pub UniError<T>);

impl<T: UniKind> Display for StdErrorWrapper<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<T: UniKind> Error for StdErrorWrapper<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.0.source()
    }
}

impl<T: UniKind> From<UniError<T>> for Box<dyn Error + Send + Sync> {
    fn from(err: UniError<T>) -> Self {
        Box::new(StdErrorWrapper(err))
    }
}

/// A wrapper for a `DynError` that implements the `Error` trait. Useful for
/// converting a `DynError` to a `Box<dyn Error + Send + Sync>` (and back via
/// downcasting).
#[derive(Debug)]
pub struct StdErrorDynWrapper(pub DynError);

impl Display for StdErrorDynWrapper {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl Error for StdErrorDynWrapper {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.0.source()
    }
}

impl From<DynError> for Box<dyn Error + Send + Sync> {
    fn from(err: DynError) -> Self {
        Box::new(StdErrorDynWrapper(err))
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

impl<T: UniKind + Default, E: UniStdError> ErrorContext<T> for E {
    fn with_kind(self, kind: T) -> UniError<T> {
        UniError::new(kind, None, Some(UniError::<T>::build_cause_error(self)))
    }

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            Default::default(),
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
            Default::default(),
            None,
            Some(UniError::<T>::build_cause_error(self)),
        )
    }
}

impl<T: UniKind + Default, U: UniKind> ErrorContext<T> for UniError<U> {
    fn with_kind(self, kind: T) -> UniError<T> {
        UniError::new(kind, None, Some(UniError::<T>::build_cause(self)))
    }

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            Default::default(),
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
            Default::default(),
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

impl<T: UniKind + Default, U, E: UniStdError> ResultContext<T, U, E> for Result<U, E> {
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

impl<T: UniKind + Default, U: UniKind + Default, V> ResultContext<U, V, T> for UniResult<V, T> {
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
    fn with_kind_disp(self, kind: T) -> UniError<T>;

    /// Wraps the existing error with the provided context (for `Display` types).
    fn with_context_disp(self, context: impl Into<Cow<'static, str>>) -> UniError<T>;

    /// Wraps the existing error with the provided kind and context (for Display types).
    fn with_kind_context_disp(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T>;

    /// Wraps the existing error with no additional context (for `Display` types).
    fn wrap_disp(self) -> UniError<T>;
}

impl<T: UniKind + Default, E: UniDisplay> ErrorContextDisplay<T> for E {
    fn with_kind_disp(self, kind: T) -> UniError<T> {
        UniError::new(kind, None, Some(UniError::<T>::build_cause_display(self)))
    }

    fn with_context_disp(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(UniError::<T>::build_cause_display(self)),
        )
    }

    fn with_kind_context_disp(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(UniError::<T>::build_cause_display(self)),
        )
    }

    fn wrap_disp(self) -> UniError<T> {
        UniError::new(
            Default::default(),
            None,
            Some(UniError::<T>::build_cause_display(self)),
        )
    }
}

// *** ResultContextDisplay ***

/// A trait for wrapping an existing result error with a additional context (for `Display` types).
pub trait ResultContextDisplay<T, U, E> {
    /// Wraps the existing result error with the provided kind (for `Display` types).
    fn with_kind_disp(self, kind: T) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided context (for `Display` types).
    fn with_context_disp(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided kind and context (for `Display` types).
    fn with_kind_context_disp(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> UniResult<U, T>;

    /// Wraps the existing result error with no additional context (for `Display` types).
    fn wrap_disp(self) -> UniResult<U, T>;
}

impl<T: UniKind + Default, U, E: UniDisplay> ResultContextDisplay<T, U, E> for Result<U, E> {
    fn with_context_disp(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.with_context_disp(context))
    }

    fn with_kind_disp(self, kind: T) -> UniResult<U, T> {
        self.map_err(|err| err.with_kind_disp(kind))
    }

    fn with_kind_context_disp(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> UniResult<U, T> {
        self.map_err(|err| err.with_kind_context_disp(kind, context))
    }

    fn wrap_disp(self) -> UniResult<U, T> {
        self.map_err(|err| err.wrap_disp())
    }
}

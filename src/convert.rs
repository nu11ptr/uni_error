use alloc::{borrow::Cow, boxed::Box};
use core::{error::Error, fmt::Display};

use crate::{
    SimpleError, UniResult,
    cause::{CauseInner, UniDisplay, UniStdError},
    error::UniError,
    kind::{UniKind, UniKindCode, UniKindCodes},
};

// *** From implementations ***

impl<K: Default, E: UniStdError> From<E> for UniError<K> {
    fn from(err: E) -> Self {
        ErrorContext::kind_default(err)
    }
}

impl<E: UniStdError> From<E> for UniError<dyn UniKind> {
    fn from(err: E) -> Self {
        SimpleError::from(err).into()
    }
}

impl<K: UniKind> From<UniError<K>> for UniError<dyn UniKind> {
    fn from(err: UniError<K>) -> Self {
        err.into_dyn_kind()
    }
}

impl<K: UniKindCode> From<UniError<K>> for UniError<dyn UniKindCode<Code = K::Code>> {
    fn from(err: UniError<K>) -> Self {
        err.into_dyn_kind_code()
    }
}

impl<K: UniKindCodes> From<UniError<K>>
    for UniError<dyn UniKindCodes<Code = K::Code, Code2 = K::Code2>>
{
    fn from(err: UniError<K>) -> Self {
        err.into_dyn_kind_codes()
    }
}

// Generic - in case the user isn't using Axum or wants to modify before returning.
#[cfg(any(feature = "http_code", feature = "axum_code"))]
impl<K: UniKindCode<Code = http::StatusCode>> From<UniError<K>>
    for (http::StatusCode, alloc::string::String)
{
    fn from(err: UniError<K>) -> Self {
        (
            err.typed_code(),
            <UniError<K> as alloc::string::ToString>::to_string(&err),
        )
    }
}

// Generic - in case the user isn't using Axum or wants to modify before returning.
#[cfg(any(feature = "http_code2", feature = "axum_code2"))]
impl<K: UniKindCodes<Code2 = http::StatusCode>> From<UniError<K>>
    for (http::StatusCode, alloc::string::String)
{
    fn from(err: UniError<K>) -> Self {
        (
            err.typed_code2(),
            <UniError<K> as alloc::string::ToString>::to_string(&err),
        )
    }
}

// Generic - in case the user wants to modify before returning.
#[cfg(feature = "tonic_code")]
impl<K: UniKindCode<Code = tonic::Code>> From<UniError<K>>
    for (tonic::Code, alloc::string::String)
{
    fn from(err: UniError<K>) -> Self {
        (
            err.typed_code(),
            <UniError<K> as alloc::string::ToString>::to_string(&err),
        )
    }
}

#[cfg(feature = "tonic_code")]
impl<K: UniKindCode<Code = tonic::Code>> From<UniError<K>> for tonic::Status {
    fn from(err: UniError<K>) -> Self {
        tonic::Status::new(
            err.typed_code(),
            <UniError<K> as alloc::string::ToString>::to_string(&err),
        )
    }
}

// Generic - in case the user wants to modify before returning.
#[cfg(feature = "tonic_code2")]
impl<K: UniKindCodes<Code2 = tonic::Code>> From<UniError<K>>
    for (tonic::Code, alloc::string::String)
{
    fn from(err: UniError<K>) -> Self {
        (
            err.typed_code2(),
            <UniError<K> as alloc::string::ToString>::to_string(&err),
        )
    }
}

#[cfg(feature = "tonic_code2")]
impl<K: UniKindCodes<Code2 = tonic::Code>> From<UniError<K>> for tonic::Status {
    fn from(err: UniError<K>) -> Self {
        tonic::Status::new(
            err.typed_code2(),
            <UniError<K> as alloc::string::ToString>::to_string(&err),
        )
    }
}

// *** IntoResponse ***

#[cfg(feature = "axum_code")]
impl<K: UniKindCode<Code = http::StatusCode>> axum::response::IntoResponse for UniError<K> {
    fn into_response(self) -> axum::response::Response {
        (
            self.typed_code(),
            <UniError<K> as alloc::string::ToString>::to_string(&self),
        )
            .into_response()
    }
}

#[cfg(feature = "axum_code2")]
impl<K: UniKindCodes<Code2 = http::StatusCode>> axum::response::IntoResponse for UniError<K> {
    fn into_response(self) -> axum::response::Response {
        (
            self.typed_code2(),
            <UniError<K> as alloc::string::ToString>::to_string(&self),
        )
            .into_response()
    }
}

/// A wrapper for a [`UniError`] that implements the [`Error`] trait. Useful for
/// converting a [`UniError`] to a `Box<dyn Error + Send + Sync>` (and back via
/// downcasting).
#[derive(Debug)]
pub struct StdErrorWrapper<K: ?Sized>(pub UniError<K>);

impl<K: UniKind + ?Sized> Display for StdErrorWrapper<K> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        Display::fmt(&self.0, f)
    }
}

impl<K: UniKind + ?Sized> Error for StdErrorWrapper<K> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.0.source()
    }
}

impl<K: UniKind + ?Sized> From<UniError<K>> for Box<dyn Error + Send + Sync> {
    fn from(err: UniError<K>) -> Self {
        Box::new(StdErrorWrapper(err))
    }
}

// *** ErrorContext ***

/// A trait for wrapping an existing error with additional context.
pub trait ErrorContext<K> {
    /// Wraps the existing error with the provided kind.
    fn kind(self, kind: K) -> UniError<K>;

    /// Wraps the existing error with the provided context and a default kind.
    fn kind_default_context(self, context: impl Into<Cow<'static, str>>) -> UniError<K>
    where
        K: Default;

    /// Wraps the existing error with the provided kind and context.
    fn kind_context(self, kind: K, context: impl Into<Cow<'static, str>>) -> UniError<K>;

    /// Wraps the existing error with no additional context and a default kind.
    fn kind_default(self) -> UniError<K>
    where
        K: Default;
}

impl<K, E: UniStdError> ErrorContext<K> for E {
    fn kind(self, kind: K) -> UniError<K> {
        UniError::new(kind, None, Some(CauseInner::from_error(self)))
    }

    fn kind_default_context(self, context: impl Into<Cow<'static, str>>) -> UniError<K>
    where
        K: Default,
    {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(CauseInner::from_error(self)),
        )
    }

    fn kind_context(self, kind: K, context: impl Into<Cow<'static, str>>) -> UniError<K> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(CauseInner::from_error(self)),
        )
    }

    fn kind_default(self) -> UniError<K>
    where
        K: Default,
    {
        UniError::new(Default::default(), None, Some(CauseInner::from_error(self)))
    }
}

// *** ResultContext ***

/// A trait for wrapping an existing result error with additional context.
pub trait ResultContext<K, T> {
    /// Wraps the existing result error with the provided kind.
    fn kind(self, kind: K) -> UniResult<T, K>;

    /// Wraps the existing result error with the provided context and a default kind.
    fn kind_default_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K>
    where
        K: Default;

    /// Wraps the existing result error with the provided kind and context.
    fn kind_context(self, kind: K, context: impl Into<Cow<'static, str>>) -> UniResult<T, K>;

    /// Wraps the existing result error with the provided kind.
    fn kind_fn<F>(self, kind: F) -> UniResult<T, K>
    where
        F: FnOnce() -> K;

    /// Wraps the existing result error with the provided context and a default kind.
    fn kind_default_context_fn<F, S>(self, context: F) -> UniResult<T, K>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K: Default;

    /// Wraps the existing result error with the provided kind and context.
    fn kind_context_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<T, K>
    where
        F: FnOnce() -> K,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>;

    /// Wraps the existing result error with no additional context and a default kind.
    fn kind_default(self) -> UniResult<T, K>
    where
        K: Default;
}

impl<K, T, E: UniStdError> ResultContext<K, T> for Result<T, E> {
    fn kind(self, kind: K) -> UniResult<T, K> {
        self.map_err(|err| err.kind(kind))
    }

    fn kind_default_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K>
    where
        K: Default,
    {
        self.map_err(|err| err.kind_default_context(context))
    }

    fn kind_context(self, kind: K, context: impl Into<Cow<'static, str>>) -> UniResult<T, K> {
        self.map_err(|err| err.kind_context(kind, context))
    }

    fn kind_fn<F>(self, kind: F) -> UniResult<T, K>
    where
        F: FnOnce() -> K,
    {
        self.map_err(|err| err.kind(kind()))
    }

    fn kind_default_context_fn<F, S>(self, context: F) -> UniResult<T, K>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K: Default,
    {
        self.map_err(|err| err.kind_default_context(context()))
    }

    fn kind_context_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<T, K>
    where
        F: FnOnce() -> K,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
    {
        self.map_err(|err| err.kind_context(kind(), context()))
    }

    fn kind_default(self) -> UniResult<T, K>
    where
        K: Default,
    {
        self.map_err(|err| err.kind_default())
    }
}

impl<K, T> ResultContext<K, T> for Option<T> {
    fn kind(self, kind: K) -> UniResult<T, K> {
        self.ok_or_else(|| UniError::from_kind(kind))
    }

    fn kind_default_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K>
    where
        K: Default,
    {
        self.ok_or_else(|| UniError::from_kind_default_context(context))
    }

    fn kind_context(self, kind: K, context: impl Into<Cow<'static, str>>) -> UniResult<T, K> {
        self.ok_or_else(|| UniError::from_kind_context(kind, context))
    }

    fn kind_fn<F>(self, kind: F) -> UniResult<T, K>
    where
        F: FnOnce() -> K,
    {
        self.ok_or_else(|| UniError::from_kind(kind()))
    }

    fn kind_default_context_fn<F, S>(self, context: F) -> UniResult<T, K>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K: Default,
    {
        self.ok_or_else(|| UniError::from_kind_default_context(context()))
    }

    fn kind_context_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<T, K>
    where
        F: FnOnce() -> K,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
    {
        self.ok_or_else(|| UniError::from_kind_context(kind(), context()))
    }

    fn kind_default(self) -> UniResult<T, K>
    where
        K: Default,
    {
        self.ok_or_else(|| UniError::from_kind(Default::default()))
    }
}

impl<K: UniKind, K2: UniKind, T> ResultContext<K2, T> for UniResult<T, K> {
    fn kind(self, kind: K2) -> UniResult<T, K2> {
        self.map_err(|err| err.kind(kind))
    }

    fn kind_default_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2>
    where
        K2: Default,
    {
        self.map_err(|err| err.kind_default_context(context))
    }

    fn kind_context(self, kind: K2, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2> {
        self.map_err(|err| err.kind_context(kind, context))
    }

    fn kind_fn<F>(self, kind: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> K2,
    {
        self.map_err(|err| err.kind(kind()))
    }

    fn kind_default_context_fn<F, S>(self, context: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K2: Default,
    {
        self.map_err(|err| err.kind_default_context(context()))
    }

    fn kind_context_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<T, K2>
    where
        F: FnOnce() -> K2,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
    {
        self.map_err(|err| err.kind_context(kind(), context()))
    }

    fn kind_default(self) -> UniResult<T, K2>
    where
        K2: Default,
    {
        self.map_err(|err| err.kind_default())
    }
}

impl<K2: UniKind, T> ResultContext<K2, T> for UniResult<T, dyn UniKind> {
    fn kind(self, kind: K2) -> UniResult<T, K2> {
        self.map_err(|err| err.kind(kind))
    }

    fn kind_default_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2>
    where
        K2: Default,
    {
        self.map_err(|err| err.kind_default_context(context))
    }

    fn kind_context(self, kind: K2, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2> {
        self.map_err(|err| err.kind_context(kind, context))
    }

    fn kind_fn<F>(self, kind: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> K2,
    {
        self.map_err(|err| err.kind(kind()))
    }

    fn kind_default_context_fn<F, S>(self, context: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K2: Default,
    {
        self.map_err(|err| err.kind_default_context(context()))
    }
    fn kind_context_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<T, K2>
    where
        F: FnOnce() -> K2,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
    {
        self.map_err(|err| err.kind_context(kind(), context()))
    }

    fn kind_default(self) -> UniResult<T, K2>
    where
        K2: Default,
    {
        self.map_err(|err| err.kind_default())
    }
}

impl<C: 'static, K2: UniKind, T> ResultContext<K2, T> for UniResult<T, dyn UniKindCode<Code = C>> {
    fn kind(self, kind: K2) -> UniResult<T, K2> {
        self.map_err(|err| err.kind(kind))
    }

    fn kind_default_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2>
    where
        K2: Default,
    {
        self.map_err(|err| err.kind_default_context(context))
    }

    fn kind_context(self, kind: K2, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2> {
        self.map_err(|err| err.kind_context(kind, context))
    }

    fn kind_fn<F>(self, kind: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> K2,
    {
        self.map_err(|err| err.kind(kind()))
    }

    fn kind_default_context_fn<F, S>(self, context: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K2: Default,
    {
        self.map_err(|err| err.kind_default_context(context()))
    }
    fn kind_context_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<T, K2>
    where
        F: FnOnce() -> K2,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
    {
        self.map_err(|err| err.kind_context(kind(), context()))
    }

    fn kind_default(self) -> UniResult<T, K2>
    where
        K2: Default,
    {
        self.map_err(|err| err.kind_default())
    }
}

impl<C: 'static, C2: 'static, K2: UniKind, T> ResultContext<K2, T>
    for UniResult<T, dyn UniKindCodes<Code = C, Code2 = C2>>
{
    fn kind(self, kind: K2) -> UniResult<T, K2> {
        self.map_err(|err| err.kind(kind))
    }

    fn kind_default_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2>
    where
        K2: Default,
    {
        self.map_err(|err| err.kind_default_context(context))
    }

    fn kind_context(self, kind: K2, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2> {
        self.map_err(|err| err.kind_context(kind, context))
    }

    fn kind_fn<F>(self, kind: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> K2,
    {
        self.map_err(|err| err.kind(kind()))
    }

    fn kind_default_context_fn<F, S>(self, context: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K2: Default,
    {
        self.map_err(|err| err.kind_default_context(context()))
    }
    fn kind_context_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<T, K2>
    where
        F: FnOnce() -> K2,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
    {
        self.map_err(|err| err.kind_context(kind(), context()))
    }

    fn kind_default(self) -> UniResult<T, K2>
    where
        K2: Default,
    {
        self.map_err(|err| err.kind_default())
    }
}

// *** UniResultContext ***

/// A trait for wrapping an existing UniResult with additional context.
pub trait UniResultContext<K, K2, T> {
    /// Maps the existing result error wit the existing kind and returns a new or wrapped error.
    fn kind_map<F>(self, f: F) -> UniResult<T, K2>
    where
        F: FnOnce(UniError<K>, K) -> UniError<K2>,
        K: Clone;

    /// Wraps the existing result error with an autoconverted kind and no additional context.
    fn kind_into(self) -> UniResult<T, K2>
    where
        K: Clone + Into<K2>;

    /// Wraps the existing result error with an autoconverted kind and the provided context.
    fn kind_into_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2>
    where
        K: Clone + Into<K2>;

    /// Wraps the existing result error with an autoconverted kind and the provided context function.
    fn kind_into_context_fn<F, S>(self, context: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K: Clone + Into<K2>;
}

impl<K: UniKind, K2, T> UniResultContext<K, K2, T> for UniResult<T, K> {
    fn kind_map<F>(self, f: F) -> UniResult<T, K2>
    where
        F: FnOnce(UniError<K>, K) -> UniError<K2>,
        K: Clone,
    {
        self.map_err(|err| err.kind_map(f))
    }

    fn kind_into(self) -> UniResult<T, K2>
    where
        K: Clone + Into<K2>,
    {
        self.map_err(|err| err.kind_into())
    }

    fn kind_into_context(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K2>
    where
        K: Clone + Into<K2>,
    {
        self.map_err(|err| err.kind_into_context(context))
    }

    fn kind_into_context_fn<F, S>(self, context: F) -> UniResult<T, K2>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K: Clone + Into<K2>,
    {
        self.map_err(|err| err.kind_into_context(context()))
    }
}

// *** ErrorContextDisplay ***

/// A trait for wrapping an existing error with a additional context (for [`Display`] types).
pub trait ErrorContextDisplay<K> {
    /// Wraps the existing error with the provided kind (for [`Display`] types).
    fn kind_disp(self, kind: K) -> UniError<K>;

    /// Wraps the existing error with the provided context and a default kind (for [`Display`] types).
    fn kind_default_context_disp(self, context: impl Into<Cow<'static, str>>) -> UniError<K>
    where
        K: Default;

    /// Wraps the existing error with the provided kind and context (for Display types).
    fn kind_context_disp(self, kind: K, context: impl Into<Cow<'static, str>>) -> UniError<K>;

    /// Wraps the existing error with no additional context and a default kind (for [`Display`] types).
    fn kind_default_disp(self) -> UniError<K>
    where
        K: Default;
}

impl<K, D: UniDisplay> ErrorContextDisplay<K> for D {
    fn kind_disp(self, kind: K) -> UniError<K> {
        UniError::new(kind, None, Some(CauseInner::from_display(self)))
    }

    fn kind_default_context_disp(self, context: impl Into<Cow<'static, str>>) -> UniError<K>
    where
        K: Default,
    {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(CauseInner::from_display(self)),
        )
    }

    fn kind_context_disp(self, kind: K, context: impl Into<Cow<'static, str>>) -> UniError<K> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(CauseInner::from_display(self)),
        )
    }

    fn kind_default_disp(self) -> UniError<K>
    where
        K: Default,
    {
        UniError::new(
            Default::default(),
            None,
            Some(CauseInner::from_display(self)),
        )
    }
}

// *** ResultContextDisplay ***

/// A trait for wrapping an existing result error with a additional context (for [`Display`] types).
pub trait ResultContextDisplay<K, T> {
    /// Wraps the existing result error with the provided kind (for [`Display`] types).
    fn kind_disp(self, kind: K) -> UniResult<T, K>;

    /// Wraps the existing result error with the provided context and a default kind (for [`Display`] types).
    fn kind_default_context_disp(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K>
    where
        K: Default;

    /// Wraps the existing result error with the provided kind and context (for [`Display`] types).
    fn kind_context_disp(self, kind: K, context: impl Into<Cow<'static, str>>) -> UniResult<T, K>;

    /// Wraps the existing result error with the provided kind.
    fn kind_disp_fn<F>(self, kind: F) -> UniResult<T, K>
    where
        F: FnOnce() -> K;

    /// Wraps the existing result error with the provided context and a default kind.
    fn kind_default_context_disp_fn<F, S>(self, context: F) -> UniResult<T, K>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K: Default;

    /// Wraps the existing result error with the provided kind and context.
    fn kind_context_disp_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<T, K>
    where
        F: FnOnce() -> K,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>;

    /// Wraps the existing result error with no additional context and a default kind (for [`Display`] types).
    fn kind_default_disp(self) -> UniResult<T, K>
    where
        K: Default;
}

impl<K, T, D: UniDisplay> ResultContextDisplay<K, T> for Result<T, D> {
    fn kind_default_context_disp(self, context: impl Into<Cow<'static, str>>) -> UniResult<T, K>
    where
        K: Default,
    {
        self.map_err(|err| err.kind_default_context_disp(context))
    }

    fn kind_disp(self, kind: K) -> UniResult<T, K> {
        self.map_err(|err| err.kind_disp(kind))
    }

    fn kind_context_disp(self, kind: K, context: impl Into<Cow<'static, str>>) -> UniResult<T, K> {
        self.map_err(|err| err.kind_context_disp(kind, context))
    }

    fn kind_disp_fn<F>(self, kind: F) -> UniResult<T, K>
    where
        F: FnOnce() -> K,
    {
        self.map_err(|err| err.kind_disp(kind()))
    }

    fn kind_default_context_disp_fn<F, S>(self, context: F) -> UniResult<T, K>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        K: Default,
    {
        self.map_err(|err| err.kind_default_context_disp(context()))
    }

    fn kind_context_disp_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<T, K>
    where
        F: FnOnce() -> K,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
    {
        self.map_err(|err| err.kind_context_disp(kind(), context()))
    }

    fn kind_default_disp(self) -> UniResult<T, K>
    where
        K: Default,
    {
        self.map_err(|err| err.kind_default_disp())
    }
}

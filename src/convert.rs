use alloc::{borrow::Cow, boxed::Box};
use core::{error::Error, fmt::Display};

use crate::{
    cause::{UniDisplay, UniStdError},
    error::{DynError, UniError, UniErrorOps, UniKind, UniResult},
};

// *** From implementations ***

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
    fn kind(self, kind: T) -> UniError<T>;

    /// Wraps the existing error with the provided context.
    fn context(self, context: impl Into<Cow<'static, str>>) -> UniError<T>;

    /// Wraps the existing error with the provided kind and context.
    fn kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T>;

    /// Wraps the existing error with no additional context.
    fn wrap(self) -> UniError<T>;
}

impl<T: UniKind + Default, E: UniStdError> ErrorContext<T> for E {
    fn kind(self, kind: T) -> UniError<T> {
        UniError::new(kind, None, Some(UniError::<T>::build_cause_error(self)))
    }

    fn context(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(UniError::<T>::build_cause_error(self)),
        )
    }

    fn kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T> {
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
    fn kind(self, kind: T) -> UniError<T> {
        UniError::new(kind, None, Some(UniError::<T>::build_cause(self)))
    }

    fn context(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(UniError::<T>::build_cause(self)),
        )
    }

    fn kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T> {
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
    fn kind(self, kind: T) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided context.
    fn context(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided kind and context.
    fn kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided kind.
    fn kind_fn<F>(self, kind: F) -> UniResult<U, T>
    where
        F: FnOnce() -> T,
        Self: Sized,
    {
        self.kind(kind())
    }

    /// Wraps the existing result error with the provided context.
    fn context_fn<F, S>(self, context: F) -> UniResult<U, T>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        Self: Sized,
    {
        self.context(context())
    }

    /// Wraps the existing result error with the provided kind and context.
    fn kind_context_fn<F, F2, S>(self, kind: F, context: F2) -> UniResult<U, T>
    where
        F: FnOnce() -> T,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        Self: Sized,
    {
        self.kind_context(kind(), context())
    }

    /// Wraps the existing result error with no additional context.
    fn wrap(self) -> UniResult<U, T>;
}

impl<T: UniKind + Default, U, E: UniStdError> ResultContext<T, U, E> for Result<U, E> {
    fn kind(self, kind: T) -> UniResult<U, T> {
        self.map_err(|err| err.kind(kind))
    }

    fn context(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.context(context))
    }

    fn kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.kind_context(kind, context))
    }

    fn wrap(self) -> UniResult<U, T> {
        self.map_err(|err| err.wrap())
    }
}

impl<T: UniKind + Default, U, E: UniStdError> ResultContext<T, U, E> for Option<U> {
    fn kind(self, kind: T) -> UniResult<U, T> {
        self.ok_or_else(|| UniError::from_kind(kind))
    }

    fn context(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.ok_or_else(|| UniError::from_context(context))
    }

    fn kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.ok_or_else(|| UniError::from_kind_context(kind, context))
    }

    fn wrap(self) -> UniResult<U, T> {
        self.ok_or_else(|| UniError::from_kind(Default::default()))
    }
}

impl<T: UniKind + Default, U: UniKind + Default, V> ResultContext<U, V, T> for UniResult<V, T> {
    fn kind(self, kind: U) -> UniResult<V, U> {
        self.map_err(|err| err.kind(kind))
    }

    fn context(self, context: impl Into<Cow<'static, str>>) -> UniResult<V, U> {
        self.map_err(|err| err.context(context))
    }

    fn kind_context(self, kind: U, context: impl Into<Cow<'static, str>>) -> UniResult<V, U> {
        self.map_err(|err| err.kind_context(kind, context))
    }

    fn wrap(self) -> UniResult<V, U> {
        self.map_err(|err| err.wrap())
    }
}

// *** ErrorContextDisplay ***

/// A trait for wrapping an existing error with a additional context (for `Display` types).
pub trait ErrorContextDisplay<T> {
    /// Wraps the existing error with the provided kind (for `Display` types).
    fn kind_disp(self, kind: T) -> UniError<T>;

    /// Wraps the existing error with the provided context (for `Display` types).
    fn context_disp(self, context: impl Into<Cow<'static, str>>) -> UniError<T>;

    /// Wraps the existing error with the provided kind and context (for Display types).
    fn kind_context_disp(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T>;

    /// Wraps the existing error with no additional context (for `Display` types).
    fn wrap_disp(self) -> UniError<T>;
}

impl<T: UniKind + Default, E: UniDisplay> ErrorContextDisplay<T> for E {
    fn kind_disp(self, kind: T) -> UniError<T> {
        UniError::new(kind, None, Some(UniError::<T>::build_cause_display(self)))
    }

    fn context_disp(self, context: impl Into<Cow<'static, str>>) -> UniError<T> {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(UniError::<T>::build_cause_display(self)),
        )
    }

    fn kind_context_disp(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniError<T> {
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
    fn kind_disp(self, kind: T) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided context (for `Display` types).
    fn context_disp(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided kind and context (for `Display` types).
    fn kind_context_disp(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniResult<U, T>;

    /// Wraps the existing result error with the provided kind.
    fn kind_fn_disp<F>(self, kind: F) -> UniResult<U, T>
    where
        F: FnOnce() -> T,
        Self: Sized,
    {
        self.kind_disp(kind())
    }

    /// Wraps the existing result error with the provided context.
    fn context_fn_disp<F, S>(self, context: F) -> UniResult<U, T>
    where
        F: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        Self: Sized,
    {
        self.context_disp(context())
    }

    /// Wraps the existing result error with the provided kind and context.
    fn kind_context_fn_disp<F, F2, S>(self, kind: F, context: F2) -> UniResult<U, T>
    where
        F: FnOnce() -> T,
        F2: FnOnce() -> S,
        S: Into<Cow<'static, str>>,
        Self: Sized,
    {
        self.kind_context_disp(kind(), context())
    }

    /// Wraps the existing result error with no additional context (for `Display` types).
    fn wrap_disp(self) -> UniResult<U, T>;
}

impl<T: UniKind + Default, U, E: UniDisplay> ResultContextDisplay<T, U, E> for Result<U, E> {
    fn context_disp(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.context_disp(context))
    }

    fn kind_disp(self, kind: T) -> UniResult<U, T> {
        self.map_err(|err| err.kind_disp(kind))
    }

    fn kind_context_disp(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.map_err(|err| err.kind_context_disp(kind, context))
    }

    fn wrap_disp(self) -> UniResult<U, T> {
        self.map_err(|err| err.wrap_disp())
    }
}

impl<T: UniKind + Default, U, E: UniDisplay> ResultContextDisplay<T, U, E> for Option<U> {
    fn kind_disp(self, kind: T) -> UniResult<U, T> {
        self.ok_or_else(|| UniError::from_kind(kind))
    }

    fn context_disp(self, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.ok_or_else(|| UniError::from_context(context))
    }

    fn kind_context_disp(self, kind: T, context: impl Into<Cow<'static, str>>) -> UniResult<U, T> {
        self.ok_or_else(|| UniError::from_kind_context(kind, context))
    }

    fn wrap_disp(self) -> UniResult<U, T> {
        self.ok_or_else(|| UniError::from_kind(Default::default()))
    }
}

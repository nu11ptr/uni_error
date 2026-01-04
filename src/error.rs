use alloc::{borrow::Cow, boxed::Box, string::String};
use core::{
    any::type_name,
    error::Error,
    fmt::{Debug, Display},
    ops::Deref,
};
#[cfg(all(feature = "backtrace", feature = "std"))]
use std::backtrace::Backtrace;

use crate::cause::{Cause, CauseInner, Chain};
use crate::inner::UniErrorInner;
use crate::kind::{UniKind, UniKindCode, UniKindCodes};

// *** UniError ***

/// A custom error type that can be used to return an error with a custom error kind.
#[derive(Debug)]
pub struct UniError<K: ?Sized> {
    inner: UniErrorInner<K>,
}

impl<K: Default> UniError<K> {
    /// Creates a new [`UniError`] with a default kind, the provided context, and no cause.
    pub fn from_context(context: impl Into<Cow<'static, str>>) -> Self {
        Self::new(Default::default(), Some(context.into()), None)
    }

    /// Creates a new [`UniError`] with a default kind and the boxed error as the cause.
    pub fn from_boxed(error: Box<dyn Error + Send + Sync>) -> Self {
        Self::new(
            Default::default(),
            None,
            Some(CauseInner::from_boxed_error(error)),
        )
    }

    /// Creates a new [`UniError`] with a default kind, the provided context and the boxed error as the cause.
    pub fn from_context_boxed(
        context: impl Into<Cow<'static, str>>,
        error: Box<dyn Error + Send + Sync>,
    ) -> Self {
        Self::new(
            Default::default(),
            Some(context.into()),
            Some(CauseInner::from_boxed_error(error)),
        )
    }
}

impl<K> UniError<K> {
    pub(crate) fn new(
        kind: K,
        context: Option<Cow<'static, str>>,
        cause: Option<CauseInner>,
    ) -> Self {
        Self {
            inner: UniErrorInner::new(kind, context, cause),
        }
    }

    /// Creates a new [`UniError`] with the provided kind and the boxed error as the cause.
    pub fn from_kind_boxed(kind: K, error: Box<dyn Error + Send + Sync>) -> Self {
        Self::new(kind, None, Some(CauseInner::from_boxed_error(error)))
    }

    /// Creates a new [`UniError`] with the provided kind, the provided context and the boxed error as the cause.
    pub fn from_kind_context_boxed(
        kind: K,
        context: impl Into<Cow<'static, str>>,
        error: Box<dyn Error + Send + Sync>,
    ) -> Self {
        Self::new(
            kind,
            Some(context.into()),
            Some(CauseInner::from_boxed_error(error)),
        )
    }

    /// Creates a new [`UniError`] with the provided kind and no context or cause.
    pub fn from_kind(kind: K) -> Self {
        Self::new(kind, None, None)
    }

    /// Creates a new [`UniError`] with the provided kind, the provided context, and no cause.
    pub fn from_kind_context(kind: K, context: impl Into<Cow<'static, str>>) -> Self {
        Self::new(kind, Some(context.into()), None)
    }

    /// Returns the concrete type name of the error.
    pub fn type_name(&self) -> &'static str {
        type_name::<Self>()
    }
}

impl<K: UniKind> UniError<K> {
    /// Erases the custom kind and returns a [`UniError`] with a `dyn UniKind` trait object.
    pub fn into_dyn_kind(self) -> UniError<dyn UniKind> {
        UniError {
            inner: self.inner.into_dyn_kind(),
        }
    }

    /// Wraps the existing error with the provided kind.
    pub fn kind<K2: UniKind>(self, kind: K2) -> UniError<K2> {
        UniError::new(kind, None, Some(CauseInner::from_uni_error(self)))
    }

    /// Wraps the existing error with the provided context.
    pub fn context<K2: UniKind>(self, context: impl Into<Cow<'static, str>>) -> UniError<K2>
    where
        K2: Default,
    {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(CauseInner::from_uni_error(self)),
        )
    }

    /// Wraps the existing error with the provided kind and context.
    pub fn kind_context<K2: UniKind>(
        self,
        kind: K2,
        context: impl Into<Cow<'static, str>>,
    ) -> UniError<K2> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(CauseInner::from_uni_error(self)),
        )
    }

    /// Wraps the existing error with no additional context.
    pub fn wrap<K2: UniKind>(self) -> UniError<K2>
    where
        K2: Default,
    {
        UniError::new(
            Default::default(),
            None,
            Some(CauseInner::from_uni_error(self)),
        )
    }
}

impl UniError<dyn UniKind> {
    /// Returns a reference to the custom kind.
    pub fn kind_dyn_ref(&self) -> &dyn UniKind {
        self.kind_ref()
    }

    /// Converts the [`UniError`] to a [`UniError<K>`] if the kind is a [`UniKind`].
    pub fn into_typed_kind<K: UniKind>(self) -> Option<UniError<K>> {
        self.inner
            .into_typed_kind::<K>()
            .map(|inner| UniError { inner })
    }

    /// Converts the [`UniError`] to a [`UniError<K>`] if the kind is a [`UniKind`].
    pub fn to_typed_kind<K: UniKind>(&self) -> Option<UniError<K>> {
        self.inner
            .to_typed_kind::<K>()
            .map(|inner| UniError { inner })
    }

    /// Returns the concrete type name of the error.
    pub fn type_name(&self) -> String {
        let start = "uni_error::error::UniError<";
        let end = ">";
        let kind_type = self.kind_ref().type_name();
        alloc::format!("{start}{kind_type}{end}")
    }

    /// Wraps the existing error with the provided kind.
    pub fn kind<K2: UniKind>(self, kind: K2) -> UniError<K2> {
        UniError::new(kind, None, Some(CauseInner::from_dyn_error(self)))
    }

    /// Wraps the existing error with the provided context.
    pub fn context<K2: UniKind>(self, context: impl Into<Cow<'static, str>>) -> UniError<K2>
    where
        K2: Default,
    {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(CauseInner::from_dyn_error(self)),
        )
    }

    /// Wraps the existing error with the provided kind and context.
    pub fn kind_context<K2: UniKind>(
        self,
        kind: K2,
        context: impl Into<Cow<'static, str>>,
    ) -> UniError<K2> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(CauseInner::from_dyn_error(self)),
        )
    }

    /// Wraps the existing error with no additional context.
    pub fn wrap<K2: UniKind>(self) -> UniError<K2>
    where
        K2: Default,
    {
        UniError::new(
            Default::default(),
            None,
            Some(CauseInner::from_dyn_error(self)),
        )
    }
}

impl<C: 'static> UniError<dyn UniKindCode<Code = C>> {
    /// Returns a reference to the custom kind.
    pub fn kind_dyn_ref(&self) -> &dyn UniKindCode<Code = C> {
        self.kind_ref()
    }

    /// Converts the [`UniError`] to a [`UniError<K>`] if the kind is a `UniKindCode<Code = C>`.
    pub fn into_typed_kind<K: UniKindCode<Code = C>>(self) -> Option<UniError<K>> {
        self.inner
            .into_typed_kind::<K>()
            .map(|inner| UniError { inner })
    }

    /// Converts the [`UniError`] to a [`UniError<K>`] if the kind is a `UniKindCode<Code = C>`.
    pub fn to_typed_kind<K: UniKindCode<Code = C>>(&self) -> Option<UniError<K>> {
        self.inner
            .to_typed_kind::<K>()
            .map(|inner| UniError { inner })
    }

    /// Returns the concrete type name of the error.
    pub fn type_name(&self) -> String {
        let start = "uni_error::error::UniError<";
        let end = ">";
        let kind_type = self.kind_ref().type_name();
        alloc::format!("{start}{kind_type}{end}")
    }

    /// Erases the custom kind and returns a [`UniError`] with a `dyn UniKind` trait object.
    pub fn into_dyn_kind(self) -> UniError<dyn UniKind> {
        UniError {
            inner: self.inner.into_dyn_kind(),
        }
    }

    /// Wraps the existing error with the provided kind.
    pub fn kind<K2: UniKind>(self, kind: K2) -> UniError<K2> {
        UniError::new(kind, None, Some(CauseInner::from_dyn_code_error(self)))
    }

    /// Wraps the existing error with the provided context.
    pub fn context<K2: UniKind>(self, context: impl Into<Cow<'static, str>>) -> UniError<K2>
    where
        K2: Default,
    {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(CauseInner::from_dyn_code_error(self)),
        )
    }

    /// Wraps the existing error with the provided kind and context.
    pub fn kind_context<K2: UniKind>(
        self,
        kind: K2,
        context: impl Into<Cow<'static, str>>,
    ) -> UniError<K2> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(CauseInner::from_dyn_code_error(self)),
        )
    }

    /// Wraps the existing error with no additional context.
    pub fn wrap<K2: UniKind>(self) -> UniError<K2>
    where
        K2: Default,
    {
        UniError::new(
            Default::default(),
            None,
            Some(CauseInner::from_dyn_code_error(self)),
        )
    }
}

impl<C: 'static, C2: 'static> UniError<dyn UniKindCodes<Code = C, Code2 = C2>> {
    /// Returns a reference to the custom kind.
    pub fn kind_dyn_ref(&self) -> &dyn UniKindCodes<Code = C, Code2 = C2> {
        self.kind_ref()
    }

    /// Converts the [`UniError`] to a [`UniError<K>`] if the kind is a `UniKindCodes<Code = C, Code2 = C2>`.
    pub fn into_typed<K: UniKindCodes<Code = C, Code2 = C2>>(self) -> Option<UniError<K>> {
        self.inner
            .into_typed_kind::<K>()
            .map(|inner| UniError { inner })
    }

    /// Converts the [`UniError`] to a [`UniError<K>`] if the kind is a `UniKindCodes<Code = C, Code2 = C2>`.
    pub fn to_typed_kind<K: UniKindCodes<Code = C, Code2 = C2>>(&self) -> Option<UniError<K>> {
        self.inner
            .to_typed_kind::<K>()
            .map(|inner| UniError { inner })
    }

    /// Returns the concrete type name of the error.
    pub fn type_name(&self) -> String {
        let start = "uni_error::error::UniError<";
        let end = ">";
        let kind_type = self.kind_ref().type_name();
        alloc::format!("{start}{kind_type}{end}")
    }

    /// Erases the custom kind and returns a [`UniError`] with a `dyn UniKind` trait object.
    pub fn into_dyn_kind(self) -> UniError<dyn UniKind> {
        UniError {
            inner: self.inner.into_dyn_kind(),
        }
    }

    /// Wraps the existing error with the provided kind.
    pub fn kind<K2: UniKind>(self, kind: K2) -> UniError<K2> {
        UniError::new(kind, None, Some(CauseInner::from_dyn_codes_error(self)))
    }

    /// Wraps the existing error with the provided context.
    pub fn context<K2: UniKind>(self, context: impl Into<Cow<'static, str>>) -> UniError<K2>
    where
        K2: Default,
    {
        UniError::new(
            Default::default(),
            Some(context.into()),
            Some(CauseInner::from_dyn_codes_error(self)),
        )
    }

    /// Wraps the existing error with the provided kind and context.
    pub fn kind_context<K2: UniKind>(
        self,
        kind: K2,
        context: impl Into<Cow<'static, str>>,
    ) -> UniError<K2> {
        UniError::new(
            kind,
            Some(context.into()),
            Some(CauseInner::from_dyn_codes_error(self)),
        )
    }

    /// Wraps the existing error with no additional context.
    pub fn wrap<K2: UniKind>(self) -> UniError<K2>
    where
        K2: Default,
    {
        UniError::new(
            Default::default(),
            None,
            Some(CauseInner::from_dyn_codes_error(self)),
        )
    }
}

impl<K: ?Sized + 'static> UniError<K> {
    /// Returns a reference to the backtrace
    #[cfg(all(feature = "backtrace", feature = "std"))]
    pub fn backtrace(&self) -> &Backtrace {
        &self.inner.backtrace()
    }

    /// Returns a reference to the custom kind.
    pub fn kind_ref(&self) -> &K {
        self.inner.kind_ref()
    }

    /// Returns true if the error is a [`SimpleError`].
    pub fn is_simple(&self) -> bool {
        self.inner.is_simple()
    }

    /// Returns a reference to the first entry in the cause chain.
    pub fn prev_cause<'e>(&'e self) -> Option<Cause<'e>> {
        self.inner.prev_cause()
    }

    /// Returns an iterator over the cause chain.
    pub fn chain(&self) -> Chain<'_> {
        Chain::new(self.prev_cause())
    }

    // TODO: Remove Option and make 'self' a possible candidate?
    /// Returns the root cause of this error. If `None` is returned then this error is the root cause.
    pub fn root_cause(&self) -> Option<Cause<'_>> {
        let mut chain = self.chain();
        let mut root = chain.next();

        for next in chain {
            root = Some(next);
        }
        root
    }

    /// Adds the provided context to the existing error.
    pub fn add_context(self, context: impl Into<Cow<'static, str>>) -> Self {
        UniError {
            inner: self.inner.add_context(context),
        }
    }
}

impl<K: UniKind + ?Sized> UniError<K> {
    /// Returns the code (typically for FFI) for this specific kind
    pub fn kind_code(&self) -> i32 {
        self.kind_ref().code(self.prev_cause())
    }

    /// Returns a 2nd code (typically for FFI) for this specific kind.
    pub fn kind_code2(&self) -> i32 {
        self.kind_ref().code2(self.prev_cause())
    }

    /// The string value of the kind, if any. This is useful for programmatic evaluation
    /// when the type is boxed in the error chain and the type is not known
    pub fn kind_value(&self) -> Cow<'static, str> {
        self.kind_ref().value(self.prev_cause())
    }

    /// Returns additional context for this specific kind, if any
    pub fn kind_context_str(&self) -> Option<Cow<'static, str>> {
        self.kind_ref().context(self.prev_cause())
    }
}

impl<K: UniKindCode> UniError<K> {
    /// Erases the custom kind and returns a [`UniError`] with a `dyn UniKindCode` trait object.
    pub fn into_dyn_kind_code(self) -> UniError<dyn UniKindCode<Code = K::Code>> {
        UniError {
            inner: self.inner.into_dyn_kind_code(),
        }
    }
}

impl<K: UniKindCode + ?Sized> UniError<K> {
    /// Returns the code (typically for FFI) for this specific kind.
    pub fn typed_code(&self) -> K::Code {
        self.kind_ref().typed_code(self.prev_cause())
    }
}

impl<K: UniKindCodes> UniError<K> {
    /// Erases the custom kind and returns a [`UniError`] with a `dyn UniKindCodes` trait object.
    pub fn into_dyn_kind_codes(
        self,
    ) -> UniError<dyn UniKindCodes<Code = K::Code, Code2 = K::Code2>> {
        UniError {
            inner: self.inner.into_dyn_kind_codes(),
        }
    }
}

impl<K: UniKindCodes + ?Sized> UniError<K> {
    /// Returns a 2nd code (typically for FFI) for this specific kind.
    pub fn typed_code2(&self) -> K::Code2 {
        self.kind_ref().typed_code2(self.prev_cause())
    }
}

impl<K: Clone> UniError<K> {
    /// Returns a clone of the custom kind.
    pub fn kind_clone(&self) -> K {
        self.inner.kind_clone()
    }

    /// Calls the provided function with the error and the custom kind, and returns a new error with possibly a different kind.
    pub fn kind_fn<F, K2>(self, f: F) -> UniError<K2>
    where
        F: FnOnce(Self, K) -> UniError<K2>,
    {
        let kind = self.kind_clone();
        f(self, kind)
    }
}

impl<K: UniKind + ?Sized> Display for UniError<K> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <UniErrorInner<K> as Display>::fmt(&self.inner, f)
    }
}

// Manually implement as derive requires K: Clone
impl<K: ?Sized> Clone for UniError<K> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<K: PartialEq + ?Sized + 'static> PartialEq for UniError<K> {
    fn eq(&self, other: &Self) -> bool {
        self.inner.eq(&other.inner)
    }
}

impl<K: UniKind + ?Sized> Deref for UniError<K> {
    type Target = dyn Error + Sync + Send + 'static;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<K: UniKind + ?Sized> AsRef<dyn Error + Sync + Send> for UniError<K> {
    fn as_ref(&self) -> &(dyn Error + Sync + Send + 'static) {
        &**self
    }
}

use alloc::borrow::Cow;
use core::{
    any::{Any, type_name},
    fmt::Debug,
};

use crate::cause::Cause;
use crate::error::UniError;

// *** UniKind trait ***

/// A trait that specifies a custom error kind. Any specified to facilitate downcasting.
pub trait UniKind: Debug + Any + Send + Sync {
    /// The string value of the kind, if any. This is useful for programmatic evaluation
    /// when the type is boxed in the error chain and the type is not known. Defaults to `""`.
    fn value(&self, _cause: Option<Cause<'_>>) -> Cow<'static, str> {
        Cow::Borrowed("")
    }

    /// Returns additional context for this specific kind, if any. Defaults to `None`.
    fn context(&self, _cause: Option<Cause<'_>>) -> Option<Cow<'static, str>> {
        None
    }

    /// Returns the code (typically for FFI) for this specific kind. Defaults to -1.
    fn code(&self, _cause: Option<Cause<'_>>) -> i32 {
        -1
    }

    /// Returns a 2nd code (typically for FFI) for this specific kind. Defaults to -1.
    fn code2(&self, _cause: Option<Cause<'_>>) -> i32 {
        -1
    }

    /// Returns the concrete type name.
    fn type_name(&self) -> &'static str {
        type_name::<Self>()
    }

    /// Converts the [`UniKind`] into a [`UniError`] with the same kind.
    fn into_error(self) -> UniError<Self>
    where
        Self: Sized,
    {
        UniError::from_kind(self)
    }
}

impl dyn UniKind {
    /// Attempts to downcast a [`UniKind`] to a specific concrete type.
    pub fn downcast_ref<K: UniKind>(&self) -> Option<&K> {
        let err: &dyn Any = self;
        err.downcast_ref()
    }
}

impl UniKind for () {}

/// A [`UniKind`] that has a typed code.
pub trait UniKindCode: UniKind {
    /// The type of the code.
    type Code;

    /// Returns the typed code for this specific kind.
    fn typed_code(&self, cause: Option<Cause<'_>>) -> Self::Code;
}

impl<C> dyn UniKindCode<Code = C> {
    /// Attempts to downcast a [`UniKindCode`] to a specific concrete type.
    pub fn downcast_ref<K: UniKindCode<Code = C>>(&self) -> Option<&K> {
        let err: &dyn Any = self;
        err.downcast_ref()
    }
}

/// A [`UniKind`] that has a two typed codes.
pub trait UniKindCodes: UniKindCode {
    /// The type of the 2nd code.
    type Code2;

    /// Returns the 2nd typed code for this specific kind.
    fn typed_code2(&self, cause: Option<Cause<'_>>) -> Self::Code2;
}

impl<C, C2> dyn UniKindCodes<Code = C, Code2 = C2> {
    /// Attempts to downcast a `UniKind` to a specific concrete type.
    pub fn downcast_ref<K: UniKindCodes<Code = C, Code2 = C2>>(&self) -> Option<&K> {
        let err: &dyn Any = self;
        err.downcast_ref()
    }
}

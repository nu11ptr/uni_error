use alloc::{borrow::Cow, boxed::Box, sync::Arc};
use core::{
    any::{Any, TypeId},
    error::Error,
    fmt::{Debug, Display},
    ops::Deref,
};

use crate::cause::{Cause, CauseInner, Chain, UniDisplay};

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

// *** UniErrorInner ***

#[derive(Debug)]
pub(crate) struct UniErrorInner<T> {
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
    pub(crate) fn new(
        kind: T,
        context: Option<Cow<'static, str>>,
        cause: Option<CauseInner>,
    ) -> Self {
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
        Chain::new(self.prev_cause())
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

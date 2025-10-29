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

/// A result type that can be used to return either a success or an error with a custom error kind.
pub type KindResult<T, U> = Result<T, KindError<U>>;

/// A result type that can be used to return either a success or a simple error.
pub type SimpleResult<T> = Result<T, SimpleError>;

/// A simple error type that can be used to return an error with no custom error kind.
pub type SimpleError = KindError<()>;

/// An error type that can be used used as a cause when unsure of T
pub type UnknownKindError = KindError<Box<dyn KindContext>>;

// *** KindContext ***

pub trait KindContext: Any {
    fn default() -> Self
    where
        Self: Sized;

    fn context(&self) -> Option<&str> {
        None
    }

    fn code(&self) -> i32 {
        -1
    }
}

impl KindContext for () {
    fn default() -> Self {
        Default::default()
    }
}

impl KindContext for Box<dyn KindContext> {
    fn default() -> Self {
        unreachable!("Cannot create a default kind for a Box<dyn KindContext>");
    }

    fn context(&self) -> Option<&str> {
        self.as_ref().context()
    }
}

// *** "My" traits ***

pub trait MyError: Error + Any {}

impl<T> MyError for T where T: Error + Any {}

pub trait MyDisplay: Display + Any {}

impl<T> MyDisplay for T where T: Display + Any {}

// *** Cause ***

pub enum Cause<T> {
    SimpleError(SimpleError),
    KindError(KindError<T>),
    UnknownKindError(UnknownKindError),
    Error(Box<dyn MyError>),
    Display(Box<dyn MyDisplay>),
}

impl<T: KindContext> Cause<T> {
    pub fn unknown_kind<U: KindContext>(&self) -> Option<&U> {
        match self {
            Cause::UnknownKindError(err) => {
                let kind: &dyn Any = &**err.kind_ref();

                match kind.downcast_ref::<U>() {
                    Some(kind) => Some(kind),
                    None => None,
                }
            }
            _ => None,
        }
    }

    pub fn as_error_type<U: MyError>(&self) -> Option<&U> {
        match self {
            Cause::Error(err) => {
                let kind: &dyn Any = &**err;
                match kind.downcast_ref::<U>() {
                    Some(kind) => Some(kind),
                    None => None,
                }
            }
            _ => None,
        }
    }

    pub fn as_display_type<U: MyDisplay>(&self) -> Option<&U> {
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

impl<T: KindContext> Debug for Cause<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl<T: KindContext> Display for Cause<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Cause::SimpleError(err) => <SimpleError as Display>::fmt(err, f),
            Cause::KindError(err) => <KindError<T> as Display>::fmt(err, f),
            Cause::UnknownKindError(err) => {
                <KindError<Box<dyn KindContext>> as Display>::fmt(err, f)
            }
            Cause::Error(err) => <Box<dyn MyError> as Display>::fmt(err, f),
            Cause::Display(err) => <Box<dyn MyDisplay> as Display>::fmt(err, f),
        }
    }
}

impl<T: KindContext> Error for Cause<T> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Cause::SimpleError(err) => err.source(),
            Cause::KindError(err) => err.source(),
            Cause::UnknownKindError(err) => err.source(),
            Cause::Error(err) => err.source(),
            Cause::Display(_) => None,
        }
    }
}

// *** KindError ***

struct KindErrorInner<T> {
    kind: T,
    context: Option<Cow<'static, str>>,
    cause: Option<Cause<T>>,
}

pub struct KindError<T> {
    inner: Box<KindErrorInner<T>>,
}

impl<T: KindContext> KindError<T> {
    fn new(kind: T, context: Option<Cow<'static, str>>, cause: Option<Cause<T>>) -> Self {
        Self {
            inner: Box::new(KindErrorInner {
                kind,
                context,
                cause,
            }),
        }
    }

    pub fn from_context(context: impl Into<Cow<'static, str>>) -> Self {
        Self::new(KindContext::default(), Some(context.into()), None)
    }

    pub fn from_kind(kind: T) -> Self {
        Self::new(kind, None, None)
    }

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
            Cause::KindError(
                *cause
                    .downcast::<KindError<T>>()
                    .expect("cause is not a KindError<T>"),
            )
        }
    }

    fn build_cause_display(cause: impl MyDisplay) -> Cause<T> {
        let is_simple_error = <dyn Any>::is::<SimpleError>(&cause);
        let is_kind_error = <dyn Any>::is::<KindError<T>>(&cause);

        if is_simple_error || is_kind_error {
            Self::build_kind_error_cause(Box::new(cause), is_simple_error)
        } else {
            Cause::Display(Box::new(cause))
        }
    }

    fn build_cause(cause: impl MyError) -> Cause<T> {
        let is_simple_error = <dyn Any>::is::<SimpleError>(&cause);
        let is_kind_error = <dyn Any>::is::<KindError<T>>(&cause);

        if is_simple_error || is_kind_error {
            Self::build_kind_error_cause(Box::new(cause), is_simple_error)
        } else {
            Cause::Error(Box::new(cause))
        }
    }

    pub fn kind_ref(&self) -> &T {
        &self.inner.kind
    }

    pub fn kind_code(&self) -> i32 {
        self.inner.kind.code()
    }

    pub fn cause(&self) -> Option<&Cause<T>> {
        self.inner.cause.as_ref()
    }
}

impl<T: Copy> KindError<T> {
    pub fn kind(&self) -> T {
        self.inner.kind
    }
}

impl<T: KindContext> Debug for KindError<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl<T: KindContext> Display for KindError<T> {
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

impl<T: KindContext> Error for KindError<T> {}

// *** ErrorContext ***

pub trait ErrorContext<T> {
    fn with_kind(self, kind: T) -> KindError<T>;

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> KindError<T>;

    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> KindError<T>;

    fn with_cause(self) -> KindError<T>;
}

impl<T: KindContext, E: MyError> ErrorContext<T> for E {
    fn with_kind(self, kind: T) -> KindError<T> {
        KindError::new(kind, None, Some(KindError::build_cause(self)))
    }

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> KindError<T> {
        KindError::new(
            KindContext::default(),
            Some(context.into()),
            Some(KindError::build_cause(self)),
        )
    }

    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> KindError<T> {
        KindError::new(
            kind,
            Some(context.into()),
            Some(KindError::build_cause(self)),
        )
    }

    fn with_cause(self) -> KindError<T> {
        KindError::new(
            KindContext::default(),
            None,
            Some(KindError::build_cause(self)),
        )
    }
}

// *** ResultContext ***

pub trait ResultContext<T, U, E> {
    fn with_kind(self, kind: T) -> KindResult<U, T>;

    fn with_context(self, context: impl Into<Cow<'static, str>>) -> KindResult<U, T>;

    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> KindResult<U, T>;

    fn with_cause(self) -> KindResult<U, T>;
}

impl<T: KindContext, U, E: MyError> ResultContext<T, U, E> for Result<U, E> {
    fn with_context(self, context: impl Into<Cow<'static, str>>) -> KindResult<U, T> {
        match self {
            Ok(value) => Ok(value),
            Err(err) => Err(err.with_context(context)),
        }
    }

    fn with_kind(self, kind: T) -> KindResult<U, T> {
        match self {
            Ok(value) => Ok(value),
            Err(err) => Err(err.with_kind(kind)),
        }
    }

    fn with_kind_context(self, kind: T, context: impl Into<Cow<'static, str>>) -> KindResult<U, T> {
        match self {
            Ok(value) => Ok(value),
            Err(err) => Err(err.with_kind_context(kind, context)),
        }
    }

    fn with_cause(self) -> KindResult<U, T> {
        match self {
            Ok(value) => Ok(value),
            Err(err) => Err(err.with_cause()),
        }
    }
}

// *** ErrorContextDisplay ***

pub trait ErrorContextDisplay<T> {
    fn with_kind_display(self, kind: T) -> KindError<T>;

    fn with_context_display(self, context: impl Into<Cow<'static, str>>) -> KindError<T>;

    fn with_kind_context_display(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> KindError<T>;

    fn with_cause_display(self) -> KindError<T>;
}

impl<T: KindContext, E: MyDisplay> ErrorContextDisplay<T> for E {
    fn with_kind_display(self, kind: T) -> KindError<T> {
        KindError::new(kind, None, Some(KindError::build_cause_display(self)))
    }

    fn with_context_display(self, context: impl Into<Cow<'static, str>>) -> KindError<T> {
        KindError::new(
            KindContext::default(),
            Some(context.into()),
            Some(KindError::build_cause_display(self)),
        )
    }

    fn with_kind_context_display(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> KindError<T> {
        KindError::new(
            kind,
            Some(context.into()),
            Some(KindError::build_cause_display(self)),
        )
    }

    fn with_cause_display(self) -> KindError<T> {
        KindError::new(
            KindContext::default(),
            None,
            Some(KindError::build_cause_display(self)),
        )
    }
}

// *** ResultContextDisplay ***

pub trait ResultContextDisplay<T, U, E> {
    fn with_kind_display(self, kind: T) -> KindResult<U, T>;

    fn with_context_display(self, context: impl Into<Cow<'static, str>>) -> KindResult<U, T>;

    fn with_kind_context_display(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> KindResult<U, T>;

    fn with_cause_display(self) -> KindResult<U, T>;
}

impl<T: KindContext, U, E: MyDisplay> ResultContextDisplay<T, U, E> for Result<U, E> {
    fn with_context_display(self, context: impl Into<Cow<'static, str>>) -> KindResult<U, T> {
        match self {
            Ok(value) => Ok(value),
            Err(err) => Err(err.with_context_display(context)),
        }
    }

    fn with_kind_display(self, kind: T) -> KindResult<U, T> {
        match self {
            Ok(value) => Ok(value),
            Err(err) => Err(err.with_kind_display(kind)),
        }
    }

    fn with_kind_context_display(
        self,
        kind: T,
        context: impl Into<Cow<'static, str>>,
    ) -> KindResult<U, T> {
        match self {
            Ok(value) => Ok(value),
            Err(err) => Err(err.with_kind_context_display(kind, context)),
        }
    }

    fn with_cause_display(self) -> KindResult<U, T> {
        match self {
            Ok(value) => Ok(value),
            Err(err) => Err(err.with_cause_display()),
        }
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

    fn propigate_error() -> KindResult<(), TestKind> {
        let test = RefCell::new(());
        let _borrow = test.borrow_mut();
        let _ = test.try_borrow_mut().with_context("test")?;
        Ok(())
    }

    #[derive(Debug, PartialEq, Eq)]
    enum TestKind {
        Test,
    }

    impl KindContext for TestKind {
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
        let err: KindError<TestKind> = KindError::from_context("test");
        assert_eq!(err.to_string(), "test");
        assert_eq!(err.kind_ref(), &TestKind::Test);
        assert!(err.cause().is_none());
    }

    #[test]
    fn test_propigate_error() {
        let err = propigate_error().unwrap_err();
        assert_eq!(err.to_string(), "test: RefCell already borrowed");
        assert_eq!(err.kind_ref(), &TestKind::Test);
        assert!(matches!(err.cause(), Some(Cause::Error(_))));
        assert!(
            err.cause()
                .unwrap()
                .as_error_type::<BorrowMutError>()
                .is_some()
        );
    }
}

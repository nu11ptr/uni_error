use alloc::{borrow::Cow, sync::Arc};
use core::{
    any::{Any, TypeId},
    error::Error,
    fmt::{Debug, Display},
};
#[cfg(all(feature = "backtrace", feature = "std"))]
use std::backtrace::Backtrace;

use crate::cause::{Cause, CauseInner};
use crate::kind::{UniKind, UniKindCode, UniKindCodes};

// *** UniErrorInner ***

// NOTE: Each piece of the inner is separated into an independent cloneable so that
// we have the option to create a new error from parts of an existing error.
#[derive(Debug)]
pub(crate) struct UniErrorInner<K: ?Sized> {
    kind: Arc<K>,
    context: Option<Cow<'static, str>>,
    cause: Option<Arc<CauseInner>>,
    #[cfg(all(feature = "backtrace", feature = "std"))]
    backtrace: Arc<Backtrace>,
}

impl<K> UniErrorInner<K> {
    pub(crate) fn new(
        kind: K,
        context: Option<Cow<'static, str>>,
        cause: Option<CauseInner>,
    ) -> Self {
        Self {
            kind: Arc::new(kind),
            context,
            cause: cause.map(Arc::new),
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: Arc::new(Backtrace::capture()),
        }
    }
}

impl<K: ?Sized + 'static> UniErrorInner<K> {
    #[cfg(all(feature = "backtrace", feature = "std"))]
    pub fn backtrace(&self) -> &Backtrace {
        &self.backtrace
    }

    pub fn kind_ref(&self) -> &K {
        &self.kind
    }

    pub fn prev_cause<'e>(&'e self) -> Option<Cause<'e>> {
        self.cause.as_ref().map(|inner| Cause::from_inner(inner))
    }

    pub fn is_simple(&self) -> bool {
        <UniErrorInner<K> as Any>::type_id(self) == TypeId::of::<UniErrorInner<()>>()
    }

    pub fn add_context(mut self, context: impl Into<Cow<'static, str>>) -> Self {
        let context = context.into();

        match self.context {
            Some(existing) => {
                self.context = Some(alloc::format!("{context}: {existing}").into());
            }
            None => {
                self.context = Some(context);
            }
        }

        self
    }
}

impl<K: Clone> UniErrorInner<K> {
    pub fn kind_clone(&self) -> K {
        (*self.kind).clone()
    }
}

impl<K: UniKind> UniErrorInner<K> {
    pub fn into_dyn_kind(self) -> UniErrorInner<dyn UniKind> {
        UniErrorInner {
            kind: self.kind as Arc<dyn UniKind>,
            context: self.context,
            cause: self.cause,
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace,
        }
    }
}

impl<K: UniKindCode> UniErrorInner<K> {
    pub fn into_dyn_kind_code(self) -> UniErrorInner<dyn UniKindCode<Code = K::Code>> {
        UniErrorInner {
            kind: self.kind as Arc<dyn UniKindCode<Code = K::Code>>,
            context: self.context,
            cause: self.cause,
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace,
        }
    }
}

impl<K: UniKindCodes> UniErrorInner<K> {
    pub fn into_dyn_kind_codes(
        self,
    ) -> UniErrorInner<dyn UniKindCodes<Code = K::Code, Code2 = K::Code2>> {
        UniErrorInner {
            kind: self.kind as Arc<dyn UniKindCodes<Code = K::Code, Code2 = K::Code2>>,
            context: self.context,
            cause: self.cause,
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace,
        }
    }
}

impl UniErrorInner<dyn UniKind> {
    pub fn into_typed_kind<K: Send + Sync + 'static>(self) -> Option<UniErrorInner<K>> {
        let kind = self.kind as Arc<dyn Any + Send + Sync>;

        kind.downcast::<K>().ok().map(|kind| UniErrorInner {
            kind,
            context: self.context,
            cause: self.cause,
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace,
        })
    }

    pub fn to_typed_kind<K: Send + Sync + 'static>(&self) -> Option<UniErrorInner<K>> {
        let kind = self.kind.clone();
        let kind = kind as Arc<dyn Any + Send + Sync>;

        kind.downcast::<K>().ok().map(|kind| UniErrorInner {
            kind,
            context: self.context.clone(),
            cause: self.cause.clone(),
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace.clone(),
        })
    }
}

impl<C: 'static> UniErrorInner<dyn UniKindCode<Code = C>> {
    pub fn into_typed_kind<K: Send + Sync + 'static>(self) -> Option<UniErrorInner<K>> {
        let kind = self.kind as Arc<dyn Any + Send + Sync>;
        kind.downcast::<K>().ok().map(|kind| UniErrorInner {
            kind,
            context: self.context,
            cause: self.cause,
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace,
        })
    }

    pub fn to_typed_kind<K: Send + Sync + 'static>(&self) -> Option<UniErrorInner<K>> {
        let kind = self.kind.clone();
        let kind = kind as Arc<dyn Any + Send + Sync>;

        kind.downcast::<K>().ok().map(|kind| UniErrorInner {
            kind,
            context: self.context.clone(),
            cause: self.cause.clone(),
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace.clone(),
        })
    }

    pub fn into_dyn_kind(self) -> UniErrorInner<dyn UniKind> {
        UniErrorInner {
            kind: self.kind as Arc<dyn UniKind>,
            context: self.context,
            cause: self.cause,
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace,
        }
    }
}

impl<C: 'static, C2: 'static> UniErrorInner<dyn UniKindCodes<Code = C, Code2 = C2>> {
    pub fn into_typed_kind<K: Send + Sync + 'static>(self) -> Option<UniErrorInner<K>> {
        let kind = self.kind as Arc<dyn Any + Send + Sync>;
        kind.downcast::<K>().ok().map(|kind| UniErrorInner {
            kind,
            context: self.context,
            cause: self.cause,
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace,
        })
    }

    pub fn to_typed_kind<K: Send + Sync + 'static>(&self) -> Option<UniErrorInner<K>> {
        let kind = self.kind.clone();
        let kind = kind as Arc<dyn Any + Send + Sync>;

        kind.downcast::<K>().ok().map(|kind| UniErrorInner {
            kind,
            context: self.context.clone(),
            cause: self.cause.clone(),
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace.clone(),
        })
    }

    pub fn into_dyn_kind(self) -> UniErrorInner<dyn UniKind> {
        UniErrorInner {
            kind: self.kind as Arc<dyn UniKind>,
            context: self.context,
            cause: self.cause,
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace,
        }
    }
}

// *** Display ***

impl<K: UniKind + ?Sized> Display for UniErrorInner<K> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut context_written = false;
        let mut kind_context_written = false;

        // *** Context ***
        if let Some(context) = &self.context
            && !context.is_empty()
        {
            f.write_str(context)?;
            context_written = true;
        }

        let cause = self.cause.as_ref().map(|inner| Cause::from_inner(inner));

        // *** Kind Context ***
        if let Some(kind_context) = self.kind.context(cause).as_ref()
            && !kind_context.is_empty()
        {
            if context_written {
                f.write_str(": ")?;
            }
            f.write_str(kind_context)?;
            kind_context_written = true;
        }

        // *** Cause ***
        if let Some(cause) = &self.prev_cause() {
            let cause = <Cause as alloc::string::ToString>::to_string(cause);

            if !cause.is_empty() {
                if context_written || kind_context_written {
                    f.write_str(": ")?;
                }
                f.write_str(&cause)?;
            }
        }

        Ok(())
    }
}

// *** PartialEq ***

impl<K: PartialEq + ?Sized + 'static> PartialEq for UniErrorInner<K> {
    fn eq(&self, other: &Self) -> bool {
        // Kind values must be equal at minimum
        if self.kind == other.kind {
            // If the kind is `()`, then the context must be equal, otherwise
            // kind equality alone is sufficient
            if self.is_simple() {
                self.context == other.context
            } else {
                true
            }
        } else {
            false
        }
    }
}

// *** Clone ***

// Manually implement as derive requires K: Clone
impl<K: ?Sized> Clone for UniErrorInner<K> {
    fn clone(&self) -> Self {
        Self {
            kind: self.kind.clone(),
            context: self.context.clone(),
            cause: self.cause.clone(),
            #[cfg(all(feature = "backtrace", feature = "std"))]
            backtrace: self.backtrace.clone(),
        }
    }
}

// *** Error ***

impl<K: UniKind + ?Sized> Error for UniErrorInner<K> {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self.prev_cause() {
            Some(Cause::UniError(err)) => Some(&**err),
            Some(Cause::UniStdError(err)) => Some(err),
            Some(Cause::StdError(err)) => Some(err),
            Some(Cause::UniDisplay(_)) | None => None,
        }
    }
}

#![cfg(any(feature = "connect_code", feature = "connect_code2"))]

use std::borrow::Cow;

use connectrpc::{ConnectError, ErrorCode};
#[cfg(feature = "connect_code2")]
use uni_error::UniKindCodes;
use uni_error::{Cause, UniError, UniKind, UniKindCode};

#[derive(Debug, Clone, Copy)]
enum ConnectKind {
    NotFound,
    Unavailable,
}

impl UniKind for ConnectKind {
    fn value(&self, _cause: Option<Cause<'_>>) -> Cow<'static, str> {
        match self {
            Self::NotFound => "not_found",
            Self::Unavailable => "unavailable",
        }
        .into()
    }
}

#[cfg(feature = "connect_code")]
impl UniKindCode for ConnectKind {
    type Code = ErrorCode;

    fn typed_code(&self, _cause: Option<Cause<'_>>) -> ErrorCode {
        match self {
            Self::NotFound => ErrorCode::NotFound,
            Self::Unavailable => ErrorCode::Unavailable,
        }
    }
}

#[cfg(not(feature = "connect_code"))]
impl UniKindCode for ConnectKind {
    type Code = i32;

    fn typed_code(&self, _cause: Option<Cause<'_>>) -> i32 {
        match self {
            Self::NotFound => 1,
            Self::Unavailable => 2,
        }
    }
}

#[cfg(feature = "connect_code2")]
impl UniKindCodes for ConnectKind {
    type Code2 = ErrorCode;

    fn typed_code2(&self, _cause: Option<Cause<'_>>) -> ErrorCode {
        match self {
            Self::NotFound => ErrorCode::NotFound,
            Self::Unavailable => ErrorCode::Unavailable,
        }
    }
}

#[cfg(feature = "connect_code")]
#[test]
fn test_connect_code_tuple() {
    let err = UniError::from_kind_context(ConnectKind::NotFound, "missing");
    let converted: (ErrorCode, String) = err.into();

    assert_eq!(converted, (ErrorCode::NotFound, "missing".to_string()));
}

#[cfg(feature = "connect_code")]
#[test]
fn test_connect_code_error() {
    let err = UniError::from_kind_context(ConnectKind::Unavailable, "offline");
    let converted: ConnectError = err.into();

    assert_eq!(converted.code, ErrorCode::Unavailable);
    assert_eq!(converted.message.as_deref(), Some("offline"));
}

#[cfg(feature = "connect_code2")]
#[test]
fn test_connect_code2_tuple() {
    let err = UniError::from_kind_context(ConnectKind::NotFound, "missing");
    let converted: (ErrorCode, String) = err.into();

    assert_eq!(converted, (ErrorCode::NotFound, "missing".to_string()));
}

#[cfg(feature = "connect_code2")]
#[test]
fn test_connect_code2_error() {
    let err = UniError::from_kind_context(ConnectKind::Unavailable, "offline");
    let converted: ConnectError = err.into();

    assert_eq!(converted.code, ErrorCode::Unavailable);
    assert_eq!(converted.message.as_deref(), Some("offline"));
}

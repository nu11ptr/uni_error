#![forbid(unsafe_code)]
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]
#![cfg_attr(docsrs, feature(doc_cfg))]

//! A simple, universal error type for Rust

extern crate alloc;

/// Module to analyze the cause chain of an error.
pub mod cause;
/// Module for converting between error types.
pub mod convert;
mod error;
mod inner;
mod kind;
#[doc = include_str!("../README.md")]
mod readme_tests {}

pub use cause::Cause;
pub use convert::{
    ErrorContext, ErrorContextDisplay, ResultContext, ResultContextDisplay, UniResultContext,
};
pub use error::*;
pub use kind::*;

// *** Type aliases ***

/// A result type that specifies a customkind.
pub type UniResult<T, K> = Result<T, UniError<K>>;

/// An error type that is used when there is no kind.
pub type SimpleError = UniError<()>;

/// A result type that specifies no kind.
pub type SimpleResult<T> = Result<T, SimpleError>;

/// A dynamic error type that specifies a dynamic kind.
pub type DynError = UniError<dyn UniKind>;

/// A result type that specifies a dynamic kind.
pub type DynResult<T> = Result<T, DynError>;

/// A dynamic error type that specifies a dynamic kind and code.
pub type DynCodeError<C> = UniError<dyn UniKindCode<Code = C>>;

/// A result type that specifies a dynamic kind and code.
pub type DynCodeResult<T, C> = Result<T, DynCodeError<C>>;

/// A dynamic error type that specifies a dynamic kind and two codes.
pub type DynCodesError<C, C2> = UniError<dyn UniKindCodes<Code = C, Code2 = C2>>;

/// A result type that specifies a dynamic kind and two codes.
pub type DynCodesResult<T, C, C2> = Result<T, DynCodesError<C, C2>>;

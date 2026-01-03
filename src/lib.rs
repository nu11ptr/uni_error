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
#[doc = include_str!("../README.md")]
mod readme_tests {}

pub use cause::Cause;
pub use convert::{ErrorContext, ErrorContextDisplay, ResultContext, ResultContextDisplay};
pub use error::*;

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

//! A simple, universal error type for Rust

extern crate alloc;

mod cause;
mod convert;
mod error;
#[doc = include_str!("../README.md")]
mod readme_tests {}

pub use cause::*;
pub use convert::*;
pub use error::*;

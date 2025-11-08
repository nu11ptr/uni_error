# uni_error

[![Crate](https://img.shields.io/crates/v/uni_error)](https://crates.io/crates/uni_error)
[![Docs](https://docs.rs/uni_error/badge.svg)](https://docs.rs/uni_error)
[![Build](https://github.com/nu11ptr/uni_error/workflows/CI/badge.svg)](https://github.com/nu11ptr/uni_error/actions)
[![codecov](https://codecov.io/github/nu11ptr/uni_error/graph/badge.svg?token=LIBztRdGNS)](https://codecov.io/github/nu11ptr/uni_error)

A simple, universal error type for Rust

## Overview

Rust has a great system for handling conditional success in the form of `Result<T, E>`, but using this in practice often leads to reinventing the wheel, especially when the program's needs are intially unknown.

I wrote this crate for myself to be my universal error type after I noticed these trends in my programs:

1. Most simple applications just need a text error for the user. That's it.

2. When building an API, dealing with FFI, or just programmatically evaluate errors, it can be necessary to have an error "kind" to disambiguate sub-errors.

3. It can sometimes be helpful to evaluate the chain of errors for determining the root cause.

The typical crates to solve these problems are `anyhow` and `thiserror`. These are great crates, but I wanted better integration between the universal error and the kind (essentially an `anyhow` that is "kind-aware"). This crate is more like `anyhow` than `thiserror`, as the latter could be seen as complementary and used to create the inner "kind".

## Install

```shell
cargo add uni_error
```

## Features

* Simple/ergonomic API
* Can wrap any error type that implements `Display` or `Error`
* Provides error cause chain with metadata
* Both type safe and dynamic (string/integer) error kind
* Dereferences to stdlib `Error` trait
* Implements `Clone`
* No dependencies
* No macros
* No `unsafe`
* Optionally `no_std` (without loss of functionality)

## Examples

The basics:

```rust
use uni_error::*;

fn do_something() -> SimpleResult<()> {
    std::fs::read("/tmp/nonexist")?;
    Ok(())
}

fn main() {
    println!("{}", do_something().unwrap_err());
}
```

Add some context:

```rust
use uni_error::*;

fn do_something() -> SimpleResult<Vec<u8>> {
    std::fs::read("/tmp/nonexist")
        .context("Oops... I wanted this to work!")
}

fn main() {
    println!("{}", do_something().unwrap_err());
}
```

Wrap a type that doesn't implement `std::error::Error`:

```rust
use uni_error::*;

fn do_something() -> Result<(), String> {
    // Try to do something very important here...
    
    Err("Doh! It didn't work".to_string())
}

fn try_do_something() -> SimpleResult<()> {
    do_something().context_disp("Oops... I wanted this to work!")
}

fn main() {
    println!("{}", try_do_something().unwrap_err());
}
```

Or use your own kind:

```rust
use std::borrow::Cow;

use uni_error::*;

#[derive(Debug, Default)]
enum MyKind {
    #[default]
    SomethingBad,
    SomethingWorse(&'static str),
}

impl UniKind for MyKind {
    fn context(&self) -> Option<Cow<'static, str>> {
        match self {
            MyKind::SomethingBad => None,
            MyKind::SomethingWorse(msg) => Some(Cow::Borrowed(msg))
        }
    }
}

fn do_something() -> UniResult<Vec<u8>, MyKind> {
    std::fs::read("/tmp/nonexist")
        .kind(MyKind::SomethingWorse("That was REALLY bad!"))
}

fn main() {
    println!("{}", do_something().unwrap_err());
}

```

## FAQ

### How do I simply propigate errors/options/results (without further context) using the question mark?

If the error type implements `std::error::Error`, or is `UniError<T>` --> `UniError<T>`/`DynError`:

```text
result?
```

`UniError<T>` --> `UniError<U>`:

```text
result.wrap()?
```

`Option<V>`:

```text
option.wrap()?
```

Fallback for `std::fmt::Display` types:

```text
result.wrap_disp()?
```

### How does equality work?

`UniError<T>`: if kind is equal, errors are equal

`SimpleError`: if context is equal, errors are equal

`DynError`: must downcast to `UniError<T>` to get equality currently

## Status

This is currently experimental, however, I am using this as my primary error type in all my work and a startup, so it will become production shortly.

## Contributions

Contributions are welcome as long they align with my vision for this crate.

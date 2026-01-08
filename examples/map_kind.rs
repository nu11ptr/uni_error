use std::borrow::Cow;

use uni_error::*;

// *** ErrKind1 ***

#[derive(Debug, Clone, Copy)]
enum ErrKind1 {
    SomeError,
}

impl UniKind for ErrKind1 {
    fn context(&self, _cause: Option<Cause<'_>>) -> Option<Cow<'static, str>> {
        match self {
            ErrKind1::SomeError => Some("some error".into()),
        }
    }
}

// *** ErrKind2 ***

#[derive(Debug, Clone, Copy)]
enum ErrKind2 {
    ErrKind1(ErrKind1),
}

impl UniKind for ErrKind2 {}

// *** Example ***

fn try_something() -> UniResult<(), ErrKind1> {
    Err(ErrKind1::SomeError.into_error())
}

fn try_something_else() -> UniResult<(), ErrKind2> {
    try_something().kind_map(|err, old_kind| {
        err.kind_context(ErrKind2::ErrKind1(old_kind), "something bad happened")
    })
}

fn main() {
    match try_something_else() {
        Ok(_) => println!("success"),
        Err(err) => println!("error: {err}"),
    }
}

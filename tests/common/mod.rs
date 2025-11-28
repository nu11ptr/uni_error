use std::{
    borrow::Cow,
    error::Error,
    fmt::{Display, Formatter},
};

use uni_error::{Cause, UniKind};

#[derive(Debug, PartialEq, Default)]
pub(crate) enum TestKind {
    #[default]
    Test,
    // FIXME: This is always used. Why showing as dead code?
    #[allow(dead_code)]
    NotATest,
}

impl UniKind for TestKind {
    fn value(&self, _cause: Option<Cause<'_>>) -> Cow<'static, str> {
        match self {
            TestKind::Test => "Test",
            TestKind::NotATest => "NotATest",
        }
        .into()
    }

    fn context(&self, _cause: Option<Cause<'_>>) -> Option<Cow<'static, str>> {
        match self {
            TestKind::Test => None,
            TestKind::NotATest => Some("This is not a test!".into()),
        }
    }

    fn code(&self, _cause: Option<Cause<'_>>) -> i32 {
        match self {
            TestKind::Test => 42,
            TestKind::NotATest => 123,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub(crate) struct TestError {
    message: String,
    cause: Option<Box<TestError>>,
}

impl TestError {
    // FIXME: Why is this detected as dead code? It is used in the tests.
    #[allow(dead_code)]
    pub fn new(message: String, cause: Option<Box<TestError>>) -> Self {
        Self { message, cause }
    }
}

impl Display for TestError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "TestError: {}", self.message)
    }
}

impl Error for TestError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.cause.as_deref().map(|e| e as &(dyn Error + 'static))
    }
}

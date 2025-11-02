use std::{
    error::Error,
    fmt::{Display, Formatter},
};

use uni_error::UniKind;

#[derive(Debug, PartialEq, Default)]
pub(crate) enum TestKind {
    #[default]
    Test,
}

impl UniKind for TestKind {}

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
        write!(f, "TestError: {}", self.message)?;
        Ok(())
    }
}

impl Error for TestError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        self.cause.as_deref().map(|e| e as &(dyn Error + 'static))
    }
}

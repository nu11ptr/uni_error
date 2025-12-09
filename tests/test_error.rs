use uni_error::{
    Cause, DynError, ErrorContext as _, SimpleError, UniError, UniErrorOps as _, UniKind as _,
};

use crate::common::{TestError, TestKind};

mod common;

#[test]
fn test_kind() {
    let error = UniError::from_kind(TestKind::NotATest);
    let kind = error.kind_ref();

    assert_eq!(kind.type_name(), "test_error::common::TestKind");
    assert_eq!(error.kind_value(), "NotATest");
    assert_eq!(error.kind_context_str(), Some("This is not a test!".into()));
    assert_eq!(error.kind_code(), 123);
}

#[test]
fn test_dynerror() {
    let err = UniError::from_kind(TestKind::NotATest);
    let error: DynError = err.clone().into();

    assert_eq!(
        error.type_name(),
        "uni_error::error::UniError<test_error::common::TestKind>"
    );
    assert_eq!(error.kind_value(), "NotATest");
    assert_eq!(error.kind_context_str(), Some("This is not a test!".into()));
    assert_eq!(error.kind_code(), 123);

    match error.downcast_ref::<TestKind>() {
        Some(err_ref) => assert_eq!(err_ref, &err),
        None => panic!("Expected downcast to TestKind"),
    }
}

#[test]
fn test_dyn_kind_code() {
    let error = UniError::from_kind(TestKind::NotATest).erase_kind_code();
    assert_eq!(error.kind_value(), "NotATest");
    assert_eq!(error.kind_context_str(), Some("This is not a test!".into()));
    assert_eq!(error.kind_code(), 123);
    assert_eq!(error.typed_code(), 123);

    let kind = error.kind_ref();
    match kind.downcast_ref::<TestKind>() {
        Some(kind) => assert_eq!(kind, &TestKind::NotATest),
        None => panic!("Expected downcast to TestKind"),
    }

    assert!(error.into_typed::<TestKind>().is_some());
}

#[test]
fn test_dyn_kind_codes() {
    let error = UniError::from_kind(TestKind::NotATest).erase_kind_codes();
    assert_eq!(error.kind_value(), "NotATest");
    assert_eq!(error.kind_context_str(), Some("This is not a test!".into()));
    assert_eq!(error.kind_code(), 123);
    assert_eq!(error.typed_code(), 123);
    assert_eq!(error.typed_code2(), 124);

    let kind = error.kind_ref();
    match kind.downcast_ref::<TestKind>() {
        Some(kind) => assert_eq!(kind, &TestKind::NotATest),
        None => panic!("Expected downcast to TestKind"),
    }

    assert!(error.into_typed::<TestKind>().is_some());
}

#[test]
fn test_root_cause() {
    let error = TestError::new("test".to_string(), None);
    let error: UniError<TestKind> = error.into();
    let error: DynError = error.into();
    let root_cause = error.root_cause();

    assert!(matches!(root_cause, Some(Cause::UniStdError(_))));
    assert_eq!(
        root_cause.unwrap().type_name(),
        "test_error::common::TestError"
    );
}

#[test]
fn test_display() {
    let error = TestError::new("testing".to_string(), None);
    let error: UniError<TestKind> = error.kind_context(TestKind::NotATest, "is this a test?");

    assert_eq!(
        error.to_string(),
        "is this a test?: This is not a test!: TestError: testing"
    );
}

#[test]
fn test_simple_error_partial_eq() {
    let error1 = SimpleError::from_context("test");
    let error2 = SimpleError::from_context("test");
    let error3 = SimpleError::from_context("test2");

    assert_eq!(error1, error2);
    assert_ne!(error1, error3);
}

#[test]
fn test_uni_error_partial_eq() {
    let error1 = UniError::from_kind_context(TestKind::Test, "test");
    let error2 = UniError::from_kind(TestKind::Test);
    let error3 = UniError::from_kind(TestKind::NotATest);

    assert_eq!(error1, error2);
    assert_ne!(error1, error3);
}

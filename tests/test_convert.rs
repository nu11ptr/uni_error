mod common;

use uni_error::cause::*;
use uni_error::convert::*;
use uni_error::*;

use crate::common::TestKind;

#[test]
fn test_wrap_simple_to_uni() {
    let err1 = SimpleError::from_context("test");
    let err2: UniError<TestKind> = err1.clone().wrap();
    let prev = err2.prev_cause().unwrap();

    assert!(matches!(prev, Cause::UniError(_)));
    assert!(prev.next().is_none());
    assert_eq!(prev.type_name(), "uni_error::error::UniError<()>");
    match prev.downcast::<(), FakeError, ()>() {
        Some(Downcast::UniError(err)) => assert_eq!(err, err1),
        _ => panic!("Expected downcast to SimpleError"),
    }
}

#[test]
fn test_wrap_uni_to_simple() {
    let err1 = UniError::from_kind_context(TestKind::Test, "test");
    let err2: SimpleError = err1.clone().wrap();
    let prev = err2.prev_cause().unwrap();

    assert!(matches!(prev, Cause::UniError(_)));
    assert!(prev.next().is_none());
    assert_eq!(
        prev.type_name(),
        "uni_error::error::UniError<test_convert::common::TestKind>"
    );
    match prev.downcast::<(), FakeError, TestKind>() {
        Some(Downcast::UniError(err)) => assert_eq!(err, err1),
        _ => panic!("Expected downcast to UniError<TestKind>"),
    }
}

#[test]
fn test_convert_uni_to_dyn_kind_and_back() {
    let err1 = UniError::from_kind_context(TestKind::Test, "test");
    let err2: UniError<dyn UniKind> = err1.clone().into();

    // We aren't wrapping, just converting
    let prev = err2.prev_cause();
    assert!(prev.is_none());

    match err2.to_typed_kind::<TestKind>() {
        Some(err) => assert_eq!(err, err1),
        None => panic!("Expected downcast to UniError<TestKind>"),
    }
    match err2.into_typed_kind::<TestKind>() {
        Some(err) => assert_eq!(err, err1),
        None => panic!("Expected downcast to UniError<TestKind>"),
    }
}

#[test]
fn test_convert_uni_to_dyn_kind_code_and_back() {
    let err1 = UniError::from_kind_context(TestKind::Test, "test");
    let err2: UniError<dyn UniKindCode<Code = i32>> = err1.clone().into();

    // We aren't wrapping, just converting
    let prev = err2.prev_cause();
    assert!(prev.is_none());

    match err2.to_typed_kind::<TestKind>() {
        Some(err) => assert_eq!(err, err1),
        None => panic!("Expected downcast to UniError<TestKind>"),
    }
    match err2.into_typed_kind::<TestKind>() {
        Some(err) => assert_eq!(err, err1),
        None => panic!("Expected downcast to UniError<TestKind>"),
    }
}

#[test]
fn test_wrap_boxed_error_to_uni_and_back() {
    let err1: Box<dyn std::error::Error + Send + Sync> = FakeError.into();
    let err2: UniError<TestKind> = UniError::from_boxed(err1);
    let prev = err2.prev_cause().unwrap();

    assert!(matches!(prev, Cause::StdError(_)));
    assert!(prev.next().is_none());
    assert_eq!(prev.type_name(), "dyn core::error::Error");
    match prev.downcast::<(), FakeError, ()>() {
        Some(Downcast::ErrorRef(err)) => assert_eq!(err, &FakeError),
        _ => panic!("Expected downcast to FakeError"),
    }
}

#[test]
fn test_wrap_error_to_uni() {
    let err1 = FakeError;
    let err2: UniError<TestKind> = err1.into();
    let prev = err2.prev_cause().unwrap();

    assert!(matches!(prev, Cause::UniStdError(_)));
    assert!(prev.next().is_none());
    assert_eq!(prev.type_name(), "uni_error::cause::FakeError");
    match prev.downcast::<(), FakeError, ()>() {
        Some(Downcast::ErrorRef(err)) => assert_eq!(err, &FakeError),
        _ => panic!("Expected downcast to FakeError"),
    }
}

#[test]
fn test_wrap_display_to_uni() {
    let err1 = "test";
    let err2: UniError<TestKind> = err1.wrap_disp();
    let prev = err2.prev_cause().unwrap();

    assert!(matches!(prev, Cause::UniDisplay(_)));
    assert!(prev.next().is_none());
    assert_eq!(prev.type_name(), "&str");
    match prev.downcast::<&str, FakeError, ()>() {
        Some(Downcast::DisplayRef(err)) => assert_eq!(err, &err1),
        _ => panic!("Expected downcast to &str"),
    }
}

#[test]
fn test_uni_to_error_and_back() {
    let err1 = UniError::from_kind_context(TestKind::Test, "test");
    let err2: Box<dyn std::error::Error + Send + Sync> = err1.clone().into();

    match err2
        .downcast::<StdErrorWrapper<TestKind>>()
        .ok()
        .map(|err| *err)
    {
        Some(err) => assert_eq!(err.0, err1),
        None => panic!("Expected downcast to UniError<TestKind>"),
    }
}

#[test]
fn test_dyn_kind_to_error_and_back() {
    let err1: UniError<dyn UniKind> = UniError::from_kind_context(TestKind::Test, "test").into();
    //let err2: UniError<dyn UniKind> = UniError::from_kind_context(TestKind::Test, "test").into();
    let err3: Box<dyn std::error::Error + Send + Sync> = err1.into();

    match err3
        .downcast::<StdErrorWrapper<dyn UniKind>>()
        .ok()
        .map(|err| *err)
    {
        Some(_err) => {
            // TODO: Need to fix PartialEq
            //assert_eq!(err.0, err2);
        }
        None => panic!("Expected downcast to UniError<TestKind>"),
    }
}

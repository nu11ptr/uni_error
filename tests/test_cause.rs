mod common;

use std::error::Error as _;

use common::{TestError, TestKind};
use uni_error::{
    Cause, DowncastRef, ErrorContext as _, ErrorContextDisplay as _, FakeError, SimpleError,
    UniError, UniErrorOps,
};

#[test]
fn test_cause_with_error_root() {
    // First level error (will be obtained via `source`)
    let err1 = TestError::new("test".to_string(), None);
    // Second level error (will be wrapped natively)
    let err2 = TestError::new("test2".to_string(), Some(Box::new(err1.clone())));
    // First level uni error (will be wrapped with context)
    let err3: SimpleError = err2.clone().context("context");
    // Second level uni error (will be wrapped with kind)
    let err4: UniError<TestKind> = err3.clone().kind(TestKind::Test);
    // Third level error (will be wrapped with default kind)
    let err5: SimpleError = err4.clone().wrap();

    let mut chain = err5.chain();
    let cause4 = chain.next().unwrap();
    let cause3 = chain.next().unwrap();
    let cause2 = chain.next().unwrap();
    let cause1 = chain.next().unwrap();
    assert!(chain.next().is_none());

    assert!(matches!(cause4, Cause::UniError(_)));
    assert!(matches!(cause3, Cause::UniError(_)));
    assert!(matches!(cause2, Cause::UniStdError(_)));
    assert!(matches!(cause1, Cause::StdError(_)));

    assert_eq!(cause4.to_string(), "context: TestError: test2");
    assert_eq!(cause3.to_string(), "context: TestError: test2");
    assert_eq!(cause2.to_string(), "TestError: test2");
    assert_eq!(cause1.to_string(), "TestError: test");

    assert_eq!(
        cause4.type_name(),
        "uni_error::error::UniError<test_cause::common::TestKind>"
    );
    assert_eq!(cause3.type_name(), "uni_error::error::UniError<()>");
    assert_eq!(cause2.type_name(), "test_cause::common::TestError");
    assert_eq!(cause1.type_name(), "dyn core::error::Error");

    match cause4.downcast_ref::<UniError<TestKind>, FakeError>() {
        Some(DowncastRef::Any(err)) => assert_eq!(err, &err4),
        _ => panic!("Expected downcast to UniError<TestKind>"),
    }
    match cause3.downcast_ref::<SimpleError, FakeError>() {
        Some(DowncastRef::Any(err)) => assert_eq!(err, &err3),
        _ => panic!("Expected downcast to SimpleError"),
    }
    match cause2.downcast_ref::<(), TestError>() {
        Some(DowncastRef::Error(err)) => assert_eq!(err, &err2),
        _ => panic!("Expected downcast to TestError"),
    }
    match cause1.downcast_ref::<(), TestError>() {
        Some(DowncastRef::Error(err)) => assert_eq!(err, &err1),
        _ => panic!("Expected downcast to TestError"),
    }

    match cause4.source() {
        Some(err) => assert!(err.to_string().contains("context")),
        None => panic!("Expected source for cause4 to be present"),
    }
    match cause3.source().unwrap().downcast_ref::<TestError>() {
        Some(err) => assert_eq!(err, &err2),
        None => panic!("Expected source for cause3 to be present"),
    }
    match cause2.source().unwrap().downcast_ref::<TestError>() {
        Some(err) => assert_eq!(err, &err1),
        None => panic!("Expected source for cause2 to be present"),
    }
    assert!(cause1.source().is_none());
}

#[test]
fn test_cause_with_display_root() {
    let err1 = "special test";
    let err2: SimpleError = err1.context_disp("special context");
    let err3: UniError<TestKind> = err2.clone().kind(TestKind::Test);

    let mut chain = err3.chain();
    let cause2 = chain.next().unwrap();
    let cause1 = chain.next().unwrap();
    assert!(chain.next().is_none());

    assert!(matches!(cause2, Cause::UniError(_)));
    assert!(matches!(cause1, Cause::UniDisplay(_)));

    assert_eq!(cause2.to_string(), "special context: special test");
    assert_eq!(cause1.to_string(), "special test");

    assert_eq!(cause2.type_name(), "uni_error::error::UniError<()>");
    assert_eq!(cause1.type_name(), "&str");

    match cause2.downcast_ref::<SimpleError, FakeError>() {
        Some(DowncastRef::Any(err)) => assert_eq!(err, &err2),
        _ => panic!("Expected downcast to SimpleError"),
    }
    match cause1.downcast_ref::<&str, FakeError>() {
        Some(DowncastRef::Any(err)) => assert_eq!(err, &err1),
        _ => panic!("Expected downcast to &str"),
    }

    assert!(cause2.source().is_none());
    assert!(cause1.source().is_none());
}

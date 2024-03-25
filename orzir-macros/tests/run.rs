#[test]
fn test() {
    let testcases = trybuild::TestCases::new();
    testcases.pass("tests/cases/module.rs");
}

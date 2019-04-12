use dpl::{parse_term, Term};
use moniker::assert_term_eq;

#[test]
fn foo() {
    let term = parse_term("Type").unwrap();
    let ty = term.infer_type().unwrap();

    assert_term_eq!(ty, Term::Type);
}

use pimu::parse_term;

#[test]
fn test_bool_program() {
    let program = include_str!("../../examples/bool");
    let term = parse_term(program).unwrap();
    term.infer_type().unwrap();
}

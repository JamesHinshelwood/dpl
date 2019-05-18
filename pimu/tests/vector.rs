use pimu::parse_term;

#[test]
fn test_vector_program() {
    let program = include_str!("../../examples/vector");
    let term = parse_term(program).unwrap();
    term.infer_type().unwrap();
}

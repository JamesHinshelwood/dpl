use pimu::parse_term;

#[test]
fn test_nat_program() {
    let program = include_str!("../../examples/nat");
    let term = parse_term(program).unwrap();
    term.infer_type().unwrap();
}

use crate::ast::Term;
use lalrpop_util::{lalrpop_mod, ParseError};
use lazy_static::lazy_static;
use std::fmt;

/// Represents a location within a string
#[derive(Clone, Debug)]
pub struct Location {
    line: usize,
    byte: usize,
}

impl fmt::Display for Location {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({},{})", self.line, self.byte)
    }
}

lalrpop_mod!(
    #[allow(clippy::all)]
    grammar
);

lazy_static! {
    static ref PARSER: grammar::TermParser = grammar::TermParser::new();
}

pub fn parse_term(term: &str) -> Result<Term, ParseError<Location, grammar::Token, &str>> {
    Ok(PARSER
        .parse(term)
        .map_err(|e| e.map_location(|l| char_to_linechar(l, term)))?
        .to_raw())
}

/// Converts a byte offset in a `&str` to a `Location`
fn char_to_linechar(offset: usize, s: &str) -> Location {
    let mut cur_offset = 0;

    for (cur_line, line) in s.lines().enumerate() {
        if cur_offset + line.len() >= offset {
            return Location {
                line: cur_line + 1,
                byte: offset - cur_offset + 1,
            };
        }

        cur_offset += line.len() + 1;
    }
    unreachable!()
}

#[cfg(test)]
mod tests {
    use super::parse_term;
    use crate::ast::Term;
    use lalrpop_util::ParseError;
    use moniker::assert_term_eq;

    #[test]
    fn repeated_pairs() {
        let term1 = parse_term("\\w.\\x.\\y.\\z.(w, x, y, z)").unwrap();
        let term2 = parse_term("\\w.\\x.\\y.\\z.(w, (x, (y, z)))").unwrap();

        assert_term_eq!(term1, term2);
    }

    #[test]
    fn repeated_products() {
        let term1 = parse_term("\\W.\\X.\\Y.\\Z.(W * X * Y * Z)").unwrap();
        let term2 = parse_term("\\W.\\X.\\Y.\\Z.(W * (X * (Y * Z)))").unwrap();

        assert_term_eq!(term1, term2);
    }

    #[test]
    fn annotated_term() {
        let term = parse_term("(unit) : Unit").unwrap();
        let expected = Term::Annot(Term::Unit.into(), Term::UnitTy.into());

        assert_term_eq!(term, expected);
    }

    #[test]
    fn repeated_application() {
        let term = parse_term("unit unit unit unit").unwrap();
        let expected = Term::App(
            Term::App(
                Term::App(Term::Unit.into(), Term::Unit.into()).into(),
                Term::Unit.into(),
            )
            .into(),
            Term::Unit.into(),
        );

        assert_term_eq!(term, expected);
    }

    #[test]
    fn empty_sum() {
        let term = parse_term("<>").unwrap();
        let expected = Term::Enum(Vec::new());

        assert_term_eq!(term, expected);
    }

    #[test]
    fn numeric_identifier() {
        let term1 = parse_term("\\1. 1").unwrap();
        let term2 = parse_term("\\x. x").unwrap();

        assert_term_eq!(term1, term2);
    }

    #[test]
    fn prime_underscore_identifer() {
        let term1 = parse_term("\\__''__. __''__").unwrap();
        let term2 = parse_term("\\x. x").unwrap();

        assert_term_eq!(term1, term2);
    }

    #[test]
    fn error_line_number() {
        let err = parse_term("Unit\n~").unwrap_err();
        if let ParseError::UnrecognizedToken {
            token: (l, _, _), ..
        } = err
        {
            assert_eq!(l.line, 2);
        } else {
            panic!("expected UnrecognizedToken");
        }
    }

    #[test]
    fn bad_token() {
        let err = parse_term("&").unwrap_err();
        if let ParseError::InvalidToken { .. } = err {
        } else {
            panic!("expected InvalidToken")
        }
    }
}

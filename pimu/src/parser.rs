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

/// Converts a byte offset in a string, to a Location
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
}

mod ast;
mod check;
mod concrete;
mod context;
mod equal;
mod error;
mod parser;
mod print;

pub use ast::Term;
pub use parser::parse_term;

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}

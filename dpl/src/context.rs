use std::collections::HashMap;
use std::fmt;

use crate::ast::Term;
use moniker::FreeVar;

#[derive(Clone, Debug)]
pub struct Context {
    type_binding: HashMap<FreeVar<String>, Term>,
    term_binding: HashMap<FreeVar<String>, Term>,
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let ty_b = self
            .type_binding
            .iter()
            .map(|(k, v)| format!("{}: {}", crate::print::print_free_var(k), v))
            .collect::<Vec<String>>()
            .join(", ");
        let tm_b = self
            .term_binding
            .iter()
            .map(|(k, v)| format!("{} = {}", crate::print::print_free_var(k), v))
            .collect::<Vec<String>>()
            .join(", ");
        write!(f, "{} ; {}", ty_b, tm_b)
    }
}

impl Context {
    pub fn new() -> Self {
        Context {
            type_binding: HashMap::new(),
            term_binding: HashMap::new(),
        }
    }

    pub fn with_type(&self, name: &FreeVar<String>, ty: &Term) -> Self {
        let mut ctx = self.clone();
        ctx.type_binding.insert(name.clone(), ty.clone());
        ctx
    }

    pub fn get_type(&self, name: &FreeVar<String>) -> Option<Term> {
        self.type_binding.get(name).map(Term::clone)
    }

    pub fn with_term(&self, name: &FreeVar<String>, tm: &Term) -> Self {
        let mut ctx = self.clone();
        ctx.term_binding.insert(name.clone(), tm.clone());
        ctx
    }

    pub fn get_term(&self, name: &FreeVar<String>) -> Option<Term> {
        self.term_binding.get(name).map(Term::clone)
    }
}

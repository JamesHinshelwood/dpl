use moniker::{BoundVar, FreeVar, Var};
use std::fmt;

use crate::ast::Term;
use moniker::{Binder, BoundTerm, Embed};

impl fmt::Display for Term {
    #[allow(clippy::many_single_char_names)]
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Term::Annot(l, r) => write!(f, "({}) : {}", l, r),
            Term::Type => write!(f, "Type"),
            Term::Var(var) => match var {
                Var::Free(var) => write!(f, "{}", print_free_var(var)),
                Var::Bound(var) => write!(f, "{}", print_bound_var(var)),
            },
            Term::Lam(scope) => {
                let (Binder(var), body) = scope.clone().unbind();
                write!(f, "(\\{}. {})", print_free_var(&var), body)
            }
            Term::App(l, r) => write!(f, "({} {})", l, r),
            Term::Pi(scope) => {
                let ((Binder(var), Embed(l)), r) = scope.clone().unbind();
                if r.free_vars().contains(&var) {
                    write!(f, "({} : {}) -> {}", print_free_var(&var), l, r)
                } else {
                    write!(f, "{} -> {}", l, r)
                }
            }
            Term::Fix(tm) => write!(f, "fix {}", tm),
            Term::Let(scope) => {
                let ((Binder(var), Embed(l)), r) = scope.clone().unbind();
                write!(f, "let {} = {} in\n{}", print_free_var(&var), l, r)
            }
            Term::Decl(scope) => {
                let ((Binder(var), Embed(l)), r) = scope.clone().unbind();
                write!(f, "let {} : {} in\n{}", print_free_var(&var), l, r)
            }
            Term::Pair(l, r) => write!(f, "({}, {})", l, r),
            Term::LetPair(scope) => {
                let (((Binder(x), Binder(y)), Embed(p)), r) = scope.clone().unbind();
                write!(
                    f,
                    "let ({}, {}) = {} in {}",
                    print_free_var(&x),
                    print_free_var(&y),
                    p,
                    r
                )
            }
            Term::Sigma(scope) => {
                let ((Binder(var), Embed(l)), r) = scope.clone().unbind();
                if r.free_vars().contains(&var) {
                    write!(f, "({} : {}) * {}", print_free_var(&var), l, r)
                } else {
                    write!(f, "({} * {})", l, r)
                }
            }
            Term::Variant(l) => write!(f, "'{}", l),
            Term::Case(s, cases) => write!(
                f,
                "case {} of {}",
                s,
                cases
                    .iter()
                    .map(|(label, body)| format!("{} -> {}", label, body))
                    .collect::<Vec<String>>()
                    .join(" | ")
            ),
            Term::Enum(ls) => write!(f, "{{{}}}", ls.join(" | ")),
            Term::Unit => write!(f, "unit"),
            Term::UnitTy => write!(f, "Unit"),
            Term::Refl => write!(f, "refl"),
            Term::EqElim(c, p, scope) => {
                let (Binder(var), t) = scope.clone().unbind();
                write!(
                    f,
                    "case[{}] {} of refl({}) -> {}",
                    c,
                    p,
                    print_free_var(&var),
                    t
                )
            }
            Term::EqTy(x, y) => write!(f, "({} = {})", x, y),
            Term::Fold(tm) => write!(f, "fold({})", tm),
            Term::Unfold(tm) => write!(f, "unfold({})", tm),
            Term::Rec(scope) => {
                let (Binder(a), scope) = scope.clone().unbind();
                let (Binder(x), body) = scope.unbind();
                write!(
                    f,
                    "~{}. \\{}. {}",
                    print_free_var(&a),
                    print_free_var(&x),
                    body
                )
            }
        }
    }
}

fn print_bound_var(var: &BoundVar<String>) -> String {
    if let Some(name) = &var.pretty_name {
        name.to_string()
    } else {
        "_".to_string()
    }
}

pub fn print_free_var(var: &FreeVar<String>) -> String {
    if let Some(name) = &var.pretty_name {
        name.to_string()
    } else {
        "_".to_string()
    }
}

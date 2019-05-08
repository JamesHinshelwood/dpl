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
            Term::First(p) => write!(f, "{}.1", p),
            Term::Second(p) => write!(f, "{}.2", p),
            Term::Sigma(scope) => {
                let ((Binder(var), Embed(l)), r) = scope.clone().unbind();
                if r.free_vars().contains(&var) {
                    write!(f, "({} : {}) * {}", print_free_var(&var), l, r)
                } else {
                    write!(f, "({} * {})", l, r)
                }
            }
            Term::Variant(lbl, tm) => write!(f, "<{} = {}>", lbl, tm),
            Term::Case(sm, annot, cases) => {
                let annot = if let Some(scope) = annot {
                    let (Binder(var), tm) = scope.clone().unbind();
                    format!("[{}. {}] ", print_free_var(&var), tm)
                } else {
                    String::new()
                };
                write!(
                    f,
                    "case {}{} of {}",
                    annot,
                    sm,
                    cases
                        .iter()
                        .map(|(label, scope)| {
                            let (Binder(var), body) = scope.clone().unbind();
                            format!("<{} = {}> -> {}", label, print_free_var(&var), body)
                        })
                        .collect::<Vec<_>>()
                        .join(" | ")
                )
            }
            Term::Enum(tys) => write!(
                f,
                "<{}>",
                tys.iter()
                    .map(|(lbl, ty)| format!("{} : {}", lbl, ty))
                    .collect::<Vec<_>>()
                    .join(" | ")
            ),
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
    //return var.to_string();
    if let Some(name) = &var.pretty_name {
        name.to_string()
    } else {
        "_".to_string()
    }
}

pub fn print_free_var(var: &FreeVar<String>) -> String {
    //return var.to_string();
    if let Some(name) = &var.pretty_name {
        name.to_string()
    } else {
        "_".to_string()
    }
}

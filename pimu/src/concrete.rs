use std::collections::HashMap;

use crate::ast::Term;
use moniker::{Binder, Embed, FreeVar, Scope, Var};

#[derive(Clone, Debug)]
pub enum ConcreteTerm {
    Annot(Box<ConcreteTerm>, Box<ConcreteTerm>),
    Type,
    Var(String),
    Lam(String, Box<ConcreteTerm>),
    App(Box<ConcreteTerm>, Box<ConcreteTerm>),
    UnnamedPi(Box<ConcreteTerm>, Box<ConcreteTerm>),
    Pi(String, Box<ConcreteTerm>, Box<ConcreteTerm>),
    Fix(Box<ConcreteTerm>),
    Let(String, Box<ConcreteTerm>, Box<ConcreteTerm>),
    Decl(String, Box<ConcreteTerm>, Box<ConcreteTerm>),
    Pair(Box<ConcreteTerm>, Box<ConcreteTerm>),
    First(Box<ConcreteTerm>),
    Second(Box<ConcreteTerm>),
    UnnamedSigma(Box<ConcreteTerm>, Box<ConcreteTerm>),
    Sigma(String, Box<ConcreteTerm>, Box<ConcreteTerm>),
    Variant(String, Box<ConcreteTerm>),
    Case(
        Box<ConcreteTerm>,
        Option<(String, Box<ConcreteTerm>)>,
        Vec<(String, String, ConcreteTerm)>,
    ),
    Enum(Vec<(String, ConcreteTerm)>),
    Unit,
    UnitTy,
    UnitElim(String, Box<ConcreteTerm>, Box<ConcreteTerm>, Box<ConcreteTerm>),
    Refl,
    EqElim(
        Box<ConcreteTerm>,
        Box<ConcreteTerm>,
        String,
        Box<ConcreteTerm>,
    ),
    EqTy(Box<ConcreteTerm>, Box<ConcreteTerm>, Box<ConcreteTerm>),
    Fold(Box<ConcreteTerm>),
    Unfold(Box<ConcreteTerm>),
    Rec(String, String, Box<ConcreteTerm>),
}

#[derive(Clone, Debug)]
struct VarMap {
    map: HashMap<String, FreeVar<String>>,
}

impl VarMap {
    fn new() -> Self {
        VarMap {
            map: HashMap::new(),
        }
    }

    /// Add `name` to the map and return the fresh var with the updated map
    fn add_var(&self, name: &str) -> (FreeVar<String>, VarMap) {
        let mut map = self.clone();
        let var = FreeVar::fresh_named(name.to_string());
        map.map.insert(name.to_string(), var.clone());
        (var, map)
    }

    /// If `name` is in the map, this will return the var. Otherwise, return a new fresh var, called `name`.
    fn get_var(&self, name: &str) -> FreeVar<String> {
        if let Some(var) = self.map.get(&name.to_string()) {
            var.clone()
        } else {
            FreeVar::fresh_named(name.to_string())
        }
    }
}

impl ConcreteTerm {
    pub fn to_raw(&self) -> Term {
        self._to_raw(VarMap::new())
    }

    fn _to_raw(&self, vars: VarMap) -> Term {
        match self {
            ConcreteTerm::Annot(tm, ty) => Term::Annot(
                tm._to_raw(vars.clone()).into(),
                ty._to_raw(vars.clone()).into(),
            ),
            ConcreteTerm::Type => Term::Type,
            ConcreteTerm::Var(name) => Term::Var(Var::Free(vars.get_var(&name))),
            ConcreteTerm::Lam(name, body) => {
                let (var, vars) = vars.add_var(name);
                Term::Lam(Scope::new(Binder(var), body._to_raw(vars).into()))
            }
            ConcreteTerm::App(lhs, rhs) => Term::App(
                lhs._to_raw(vars.clone()).into(),
                rhs._to_raw(vars.clone()).into(),
            ),
            ConcreteTerm::UnnamedPi(l, r) => Term::Pi(Scope::new(
                (
                    Binder(FreeVar::fresh_unnamed()),
                    Embed(l._to_raw(vars.clone()).into()),
                ),
                r._to_raw(vars.clone()).into(),
            )),
            ConcreteTerm::Pi(name, l, r) => {
                let (var, new_vars) = vars.add_var(name);
                Term::Pi(Scope::new(
                    (Binder(var), Embed(l._to_raw(vars).into())),
                    r._to_raw(new_vars).into(),
                ))
            }
            ConcreteTerm::Fix(tm) => Term::Fix(tm._to_raw(vars).into()),
            ConcreteTerm::Let(name, l, r) => {
                let (var, new_vars) = vars.add_var(name);
                Term::Let(Scope::new(
                    (Binder(var), Embed(l._to_raw(vars).into())),
                    r._to_raw(new_vars).into(),
                ))
            }
            ConcreteTerm::Decl(name, l, r) => {
                let (var, new_vars) = vars.add_var(name);
                Term::Decl(Scope::new(
                    (Binder(var), Embed(l._to_raw(vars.clone()).into())),
                    r._to_raw(new_vars).into(),
                ))
            }
            ConcreteTerm::Pair(l, r) => Term::Pair(
                l._to_raw(vars.clone()).into(),
                r._to_raw(vars.clone()).into(),
            ),
            ConcreteTerm::First(p) => Term::First(p._to_raw(vars).into()),
            ConcreteTerm::Second(p) => Term::Second(p._to_raw(vars).into()),
            ConcreteTerm::UnnamedSigma(l, r) => Term::Sigma(Scope::new(
                (
                    Binder(FreeVar::fresh_unnamed()),
                    Embed(l._to_raw(vars.clone()).into()),
                ),
                r._to_raw(vars.clone()).into(),
            )),
            ConcreteTerm::Sigma(name, l, r) => {
                let (var, new_vars) = vars.add_var(name);
                Term::Sigma(Scope::new(
                    (Binder(var), Embed(l._to_raw(vars.clone()).into())),
                    r._to_raw(new_vars).into(),
                ))
            }
            ConcreteTerm::Variant(lbl, tm) => {
                Term::Variant(lbl.to_string(), tm._to_raw(vars.clone()).into())
            }
            ConcreteTerm::Case(sm, annot, cases) => Term::Case(
                sm._to_raw(vars.clone()).into(),
                annot.clone().map(|(name, tm)| {
                    let (var, new_vars) = vars.add_var(&name);
                    Scope::new(Binder(var), tm._to_raw(new_vars.clone()).into())
                }),
                cases
                    .iter()
                    .map(|(lbl, name, tm)| {
                        let (var, new_vars) = vars.add_var(&name);
                        (
                            lbl.to_string(),
                            Scope::new(Binder(var), tm._to_raw(new_vars.clone())),
                        )
                    })
                    .collect(),
            ),
            ConcreteTerm::Enum(tys) => Term::Enum(
                tys.iter()
                    .map(|(lbl, ty)| (lbl.to_string(), ty._to_raw(vars.clone())))
                    .collect(),
            ),
            ConcreteTerm::Unit => Term::Unit,
            ConcreteTerm::UnitTy => Term::UnitTy,
            ConcreteTerm::UnitElim(name, ty, unit, body) => {
                let (var, new_vars) = vars.add_var(name);
                Term::UnitElim(Scope::new(Binder(var), ty._to_raw(new_vars).into()), unit._to_raw(vars.clone()).into(), body._to_raw(vars.clone()).into())
            }
            ConcreteTerm::Refl => Term::Refl,
            ConcreteTerm::EqElim(c, p, name, t) => {
                let (var, new_vars) = vars.add_var(name);
                Term::EqElim(
                    c._to_raw(vars.clone()).into(),
                    p._to_raw(vars.clone()).into(),
                    Scope::new(Binder(var), t._to_raw(new_vars).into()),
                )
            }
            ConcreteTerm::EqTy(x, y, ty) => Term::EqTy(
                x._to_raw(vars.clone()).into(),
                y._to_raw(vars.clone()).into(),
                ty._to_raw(vars.clone()).into(),
            ),
            ConcreteTerm::Fold(tm) => Term::Fold(tm._to_raw(vars).into()),
            ConcreteTerm::Unfold(tm) => Term::Unfold(tm._to_raw(vars).into()),
            ConcreteTerm::Rec(a, x, body) => {
                let (a_var, new_vars) = vars.add_var(a);
                let (x_var, new_vars) = new_vars.add_var(x);
                Term::Rec(Scope::new(
                    Binder(a_var),
                    Scope::new(Binder(x_var), body._to_raw(new_vars).into()),
                ))
            }
        }
    }
}

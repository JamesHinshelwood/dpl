use moniker::{Binder, BoundTerm, Embed, Scope, Var};

type NameRepr = String;
pub type Name = Var<NameRepr>;

#[allow(clippy::type_complexity)]
#[derive(Clone, Debug, BoundTerm)]
pub enum Term {
    Annot(Box<Term>, Box<Term>),
    Type,
    Var(Name),
    Lam(Scope<Binder<NameRepr>, Box<Term>>),
    App(Box<Term>, Box<Term>),
    Pi(Scope<(Binder<NameRepr>, Embed<Box<Term>>), Box<Term>>),
    Fix(Box<Term>),
    Let(Scope<(Binder<NameRepr>, Embed<Box<Term>>), Box<Term>>),
    Decl(Scope<(Binder<NameRepr>, Embed<Box<Term>>), Box<Term>>),
    Pair(Box<Term>, Box<Term>),
    First(Box<Term>),
    Second(Box<Term>),
    Sigma(Scope<(Binder<NameRepr>, Embed<Box<Term>>), Box<Term>>),
    Variant(String),
    Case(Box<Term>, Vec<(String, Term)>),
    Enum(Vec<String>),
    Unit,
    UnitTy,
    Refl,
    EqElim(Box<Term>, Box<Term>, Scope<Binder<NameRepr>, Box<Term>>),
    EqTy(Box<Term>, Box<Term>),
    Fold(Box<Term>),
    Unfold(Box<Term>),
    Rec(Scope<Binder<NameRepr>, Scope<Binder<NameRepr>, Box<Term>>>),
}

pub fn lookup<T: PartialEq, U: Clone>(t: &T, v: &[(T, U)]) -> Option<U> {
    v.iter().find(|(x, _)| x == t).map(|(_, y)| y.clone())
}

impl Term {
    pub fn subst<N: PartialEq<Name>>(&self, name: &N, replacement: &Term) -> Self {
        match self {
            Term::Annot(tm, annot) => Term::Annot(
                tm.subst(name, replacement).into(),
                annot.subst(name, replacement).into(),
            ),
            Term::Type => self.clone(),
            Term::Var(var) if name == var => replacement.clone(),
            Term::Var(_) => self.clone(),
            Term::Lam(scope) => Term::Lam(Scope {
                unsafe_pattern: scope.unsafe_pattern.clone(),
                unsafe_body: scope.unsafe_body.subst(name, replacement).into(),
            }),
            Term::App(lhs, rhs) => Term::App(
                lhs.subst(name, replacement).into(),
                rhs.subst(name, replacement).into(),
            ),
            Term::Pi(scope) => {
                let (var, Embed(l)) = &scope.unsafe_pattern;
                Term::Pi(Scope {
                    unsafe_pattern: (var.clone(), Embed(l.subst(name, replacement).into())),
                    unsafe_body: scope.unsafe_body.subst(name, replacement).into(),
                })
            }
            Term::Fix(tm) => Term::Fix(tm.subst(name, replacement).into()),
            Term::Let(scope) => {
                let (var, Embed(l)) = &scope.unsafe_pattern;
                Term::Let(Scope {
                    unsafe_pattern: (var.clone(), Embed(l.subst(name, replacement).into())),
                    unsafe_body: scope.unsafe_body.subst(name, replacement).into(),
                })
            }
            Term::Decl(scope) => {
                let (var, Embed(l)) = &scope.unsafe_pattern;
                Term::Decl(Scope {
                    unsafe_pattern: (var.clone(), Embed(l.subst(name, replacement).into())),
                    unsafe_body: scope.unsafe_body.subst(name, replacement).into(),
                })
            }
            Term::Pair(lhs, rhs) => Term::Pair(
                lhs.subst(name, replacement).into(),
                rhs.subst(name, replacement).into(),
            ),
            Term::First(tm) => Term::First(tm.subst(name, replacement).into()),
            Term::Second(tm) => Term::Second(tm.subst(name, replacement).into()),
            Term::Sigma(scope) => {
                let (var, Embed(l)) = &scope.unsafe_pattern;
                Term::Sigma(Scope {
                    unsafe_pattern: (var.clone(), Embed(l.subst(name, replacement).into())),
                    unsafe_body: scope.unsafe_body.subst(name, replacement).into(),
                })
            }
            Term::Variant(l) => Term::Variant(l.to_string()),
            Term::Case(s, cases) => Term::Case(
                s.subst(name, replacement).into(),
                cases
                    .iter()
                    .map(|(l, tm)| (l.to_string(), tm.subst(name, replacement)))
                    .collect(),
            ),
            Term::Enum(ls) => Term::Enum(ls.to_vec()),
            Term::Unit => Term::Unit,
            Term::UnitTy => Term::UnitTy,
            Term::Refl => Term::Refl,
            Term::EqElim(c, p, scope) => Term::EqElim(
                c.subst(name, replacement).into(),
                p.subst(name, replacement).into(),
                Scope {
                    unsafe_pattern: scope.unsafe_pattern.clone(),
                    unsafe_body: scope.unsafe_body.subst(name, replacement).into(),
                },
            ),
            Term::EqTy(x, y) => Term::EqTy(
                x.subst(name, replacement).into(),
                y.subst(name, replacement).into(),
            ),
            Term::Fold(tm) => Term::Fold(tm.subst(name, replacement).into()),
            Term::Unfold(tm) => Term::Unfold(tm.subst(name, replacement).into()),
            Term::Rec(scope) => Term::Rec(Scope {
                unsafe_pattern: scope.unsafe_pattern.clone(),
                unsafe_body: Scope {
                    unsafe_pattern: scope.unsafe_body.unsafe_pattern.clone(),
                    unsafe_body: scope
                        .unsafe_body
                        .unsafe_body
                        .subst(name, replacement)
                        .into(),
                },
            }),
        }
    }
}

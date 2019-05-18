use crate::ast::{lookup, Term};
use crate::context::Context;
use moniker::{Binder, BoundTerm, Embed, Scope, Var};

impl Term {
    pub fn beq(&self, other: &Self, ctx: &Context) -> bool {
        Term::term_eq(&self.nf(ctx), &other.nf(ctx))
    }

    pub fn normalize(&self) -> Self {
        self.nf(&Context::new())
    }

    pub fn nf(&self, ctx: &Context) -> Self {
        match self {
            Term::Annot(tm, _) => tm.nf(ctx),
            Term::Type => Term::Type,
            Term::Var(Var::Free(var)) => {
                if let Some(tm) = ctx.get_term(var) {
                    tm.nf(ctx)
                } else {
                    Term::Var(Var::Free(var.clone()))
                }
            }
            Term::Var(Var::Bound(_)) => unreachable!(),
            Term::Lam(scope) => {
                let (var, body) = scope.clone().unbind();
                Term::Lam(Scope::new(var, body.nf(ctx).into()))
            }
            Term::App(lhs, rhs) => {
                let lhs = lhs.nf(ctx);
                let rhs = rhs.nf(ctx);
                if let Term::Lam(scope) = lhs {
                    let (Binder(var), body) = scope.unbind();
                    body.subst(&var, &rhs).nf(ctx)
                } else if let Term::App(fix, ind) = lhs.clone() {
                    if let Term::Fix(f) = *fix {
                        if let Term::Fold(rec) = rhs {
                            Term::App(
                                Term::App(Term::App(f.clone(), Term::Fix(f).into()).into(), ind)
                                    .into(),
                                Term::Fold(rec).into(),
                            )
                            .nf(ctx)
                        } else {
                            Term::App(lhs.into(), rhs.into())
                        }
                    } else {
                        Term::App(lhs.into(), rhs.into())
                    }
                } else {
                    Term::App(lhs.into(), rhs.into())
                }
            }
            Term::Pi(scope) => {
                let ((var, Embed(l)), r) = scope.clone().unbind();
                Term::Pi(Scope::new((var, Embed(l.nf(ctx).into())), r.nf(ctx).into()))
            }
            Term::Fix(tm) => Term::Fix(tm.nf(ctx).into()),
            Term::Let(scope) => {
                let ((var, Embed(l)), r) = scope.clone().unbind();
                r.subst(&var, &l).nf(ctx)
            }
            Term::Decl(scope) => {
                let ((var, Embed(l)), r) = scope.clone().unbind();
                Term::Decl(Scope::new((var, Embed(l.nf(ctx).into())), r.nf(ctx).into()))
            }
            Term::Pair(l, r) => Term::Pair(l.nf(ctx).into(), r.nf(ctx).into()),
            Term::First(p) => {
                let p = p.nf(ctx);
                if let Term::Pair(l, _) = p {
                    l.nf(ctx)
                } else {
                    Term::First(p.into())
                }
            }
            Term::Second(p) => {
                let p = p.nf(ctx);
                if let Term::Pair(_, r) = p {
                    r.nf(ctx)
                } else {
                    Term::Second(p.into())
                }
            }
            Term::Sigma(scope) => {
                let ((var, Embed(l)), r) = scope.clone().unbind();
                Term::Sigma(Scope::new((var, Embed(l.nf(ctx).into())), r.nf(ctx).into()))
            }
            Term::Variant(lbl, tm) => Term::Variant(lbl.to_string(), tm.nf(ctx).into()),
            Term::Case(s, annot, cases) => {
                let s = s.nf(ctx);
                let cases: Vec<_> = cases
                    .iter()
                    .map(|(lbl, scope)| {
                        let (var, body) = scope.clone().unbind();

                        (lbl.to_string(), Scope::new(var, body.nf(ctx)))
                    })
                    .collect();
                if let Term::Variant(lbl, tm) = s.clone() {
                    if let Some(scope) = lookup(&lbl, &cases) {
                        let (Binder(var), body) = scope.unbind();
                        body.subst(&var, &tm).nf(ctx)
                    } else {
                        Term::Case(s.into(), annot.clone(), cases.to_vec())
                    }
                } else {
                    Term::Case(s.into(), annot.clone(), cases.to_vec())
                }
            }
            Term::Enum(tys) => Term::Enum(
                tys.iter()
                    .map(|(lbl, ty)| (lbl.to_string(), ty.nf(ctx)))
                    .collect(),
            ),
            Term::Unit => Term::Unit,
            Term::UnitTy => Term::UnitTy,
            Term::UnitElim(scope, unit, body) => {
                let (var, ty) = scope.clone().unbind();
                let ty = ty.nf(ctx);
                let unit = unit.nf(ctx);
                let body = body.nf(ctx);
                if let Term::Unit = unit {
                    body
                } else {
                    Term::UnitElim(Scope::new(var, ty.into()), unit.into(), body.into())
                }
            }
            Term::Refl => Term::Refl,
            Term::EqElim(c, p, scope) => {
                let c = c.nf(ctx);
                let p = p.nf(ctx);
                let (x, t) = scope.clone().unbind();
                let t = t.nf(ctx);
                if let Term::Refl = p {
                    t
                } else {
                    Term::EqElim(c.into(), p.into(), Scope::new(x, t.into()))
                }
            }
            Term::EqTy(x, y, ty) => {
                Term::EqTy(x.nf(ctx).into(), y.nf(ctx).into(), ty.nf(ctx).into())
            }
            Term::Fold(tm) => {
                let tm = tm.nf(ctx);
                if let Term::Unfold(inner) = tm {
                    inner.nf(ctx)
                } else {
                    Term::Fold(tm.into())
                }
            }
            Term::Unfold(tm) => {
                let tm = tm.nf(ctx);
                if let Term::Fold(inner) = tm {
                    inner.nf(ctx)
                } else {
                    Term::Unfold(tm.into())
                }
            }
            Term::Rec(scope) => {
                let (a, scope) = scope.clone().unbind();
                let (x, body) = scope.unbind();
                Term::Rec(Scope::new(a, Scope::new(x, body.nf(ctx).into())))
            }
        }
    }
}

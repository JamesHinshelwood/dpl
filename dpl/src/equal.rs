use crate::ast::{lookup, Term};
use crate::context::Context;
use moniker::{Binder, BoundTerm, Embed, Scope, Var};

impl Term {
    pub fn beq(&self, other: &Self, ctx: &Context) -> bool {
        Term::term_eq(&self.nf(ctx), &other.nf(ctx))
    }

    pub fn nf(&self, ctx: &Context) -> Self {
        //println!("normalizting {}", self);
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
                    body.subst(&var, &rhs).nf(ctx) // TODO: Consider using ctx.with_term instead
                } else {
                    Term::App(lhs.into(), rhs.into())
                }
            }
            Term::Pi(scope) => {
                let ((var, Embed(l)), r) = scope.clone().unbind();
                Term::Pi(Scope::new((var, Embed(l.nf(ctx).into())), r.nf(ctx).into()))
            }
            Term::Fix(tm) => {
                let tm = tm.nf(ctx);
                if let Term::Lam(scope) = tm.clone() {
                    let (Binder(var), body) = scope.unbind();
                    body.subst(&var, &Term::Fix(tm.into())).nf(ctx)
                } else {
                    Term::Fix(tm.into())
                }
            }
            Term::Let(scope) => {
                let ((var, Embed(l)), r) = scope.clone().unbind();
                //r.subst(&var, &l) // TODO: Explicit subst
                Term::Let(Scope::new((var, Embed(l.nf(ctx).into())), r.nf(ctx).into()))
            }
            Term::Decl(scope) => {
                let ((var, Embed(l)), r) = scope.clone().unbind();
                Term::Decl(Scope::new((var, Embed(l.nf(ctx).into())), r.nf(ctx).into()))
            }
            Term::Pair(l, r) => Term::Pair(l.nf(ctx).into(), r.nf(ctx).into()),
            Term::LetPair(scope) => {
                let (((Binder(x), Binder(y)), Embed(p)), rest) = scope.clone().unbind();
                let p = p.nf(ctx);
                if let Term::Pair(l, r) = p {
                    rest.nf(&ctx.with_term(&x, &l).with_term(&y, &r))
                } else {
                    Term::LetPair(scope.clone())
                }
            }
            Term::Sigma(scope) => {
                let ((var, Embed(l)), r) = scope.clone().unbind();
                Term::Sigma(Scope::new((var, Embed(l.nf(ctx).into())), r.nf(ctx).into()))
            }
            Term::Variant(l) => Term::Variant(l.to_string()),
            Term::Case(s, cases) => {
                let s = s.nf(ctx);
                if let Term::Variant(l) = s.clone() {
                    if let Some(body) = lookup(&l, &cases) {
                        body.nf(ctx)
                    } else {
                        Term::Case(s.into(), cases.to_vec())
                    }
                } else {
                    Term::Case(s.into(), cases.to_vec())
                }
            }
            Term::Enum(ls) => Term::Enum(ls.to_vec()),
            Term::Unit => Term::Unit,
            Term::UnitTy => Term::UnitTy,
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
            Term::EqTy(x, y) => Term::EqTy(x.nf(ctx).into(), y.nf(ctx).into()),
            Term::Fold(tm) => Term::Fold(tm.nf(ctx).into()),
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

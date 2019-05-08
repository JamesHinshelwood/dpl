use crate::ast::{lookup, Term};
use crate::context::Context;
use moniker::{Binder, BoundTerm, Embed, Scope, Var};

impl Term {
    fn inferable(&self) -> bool {
        match self {
            Term::Annot(_, _) => true,
            Term::Type => true,
            Term::Var(_) => true,
            Term::App(_, _) => true,
            Term::Pi(_) => true,
            Term::Let(_) => true,
            Term::Decl(_) => unimplemented!(),
            Term::First(_) => true,
            Term::Second(_) => true,
            Term::Sigma(_) => true,
            Term::Case(_, Some(_), _) => true,
            Term::Enum(_) => true,
            Term::Unit => true,
            Term::UnitTy => true,
            Term::EqElim(_, _, _) => true,
            Term::EqTy(_, _) => true,
            Term::Unfold(_) => true,
            _ => false,
        }
    }

    pub fn eval(&self, ctx: &Context, rm_annot: bool) -> Self {
        match self {
            Term::Annot(tm, _) if rm_annot || tm.inferable() => tm.eval(ctx, rm_annot), // The annotation is only thrown away if we can infer `tm`'s type
            Term::Annot(tm, ty) => Term::Annot(tm.eval(ctx, rm_annot).into(), ty.eval(ctx, rm_annot).into()),
            Term::Type => Term::Type,
            Term::Var(Var::Free(var)) => {
                println!("looking for {}", var);
                if let Some(tm) = ctx.get_term(var) {
                    println!("found it {}", tm);
                    tm.eval(ctx, rm_annot)
                } else {
                    Term::Var(Var::Free(var.clone()))
                }
            }
            Term::Var(Var::Bound(_)) => unreachable!(),
            Term::Lam(scope) => {
                let (var, body) = scope.clone().unbind();
                Term::Lam(Scope::new(var, body.eval(ctx, rm_annot).into()))
            }
            Term::App(lhs, rhs) => {
                if let Term::Annot(tm, ty) = lhs.eval(ctx, rm_annot) {
                    match (*tm, *ty) {
                        (Term::Lam(lam_scope), Term::Pi(pi_scope)) => {
                            let (Binder(var), body) = lam_scope.unbind();
                            let ((Binder(pi_var), Embed(arg_ty)), ret_ty) = pi_scope.unbind();
                            let rhs_ann = Term::Annot(rhs.clone(), arg_ty);
                            Term::Annot(body.subst(&var, &rhs_ann).eval(ctx, rm_annot).into(), ret_ty.subst(&pi_var, &rhs_ann).eval(ctx, rm_annot).into()) //TODO: eval on outside of annot?
                        },
                        (Term::Fix(tm), Term::Pi(pi_scope)) => {
                            if let Term::Lam(lam_scope) = *tm.clone() {
                                let (Binder(f_var), body) = lam_scope.unbind();
                                if let Term::Lam(lam_scope) = *body {
                                    let (Binder(x_var), body) = lam_scope.unbind();
                                    let ((Binder(pi_var), Embed(arg_ty)), ret_ty) = pi_scope.clone().unbind();
                                    let rhs_ann = Term::Annot(rhs.clone(), arg_ty);
                                    let fix_ann = Term::Annot(Term::Fix(tm.clone()).into(), Term::Pi(pi_scope.clone()).into());
                                    Term::Annot(
                                        body.subst(&x_var, &rhs_ann).subst(&f_var, &fix_ann).eval(ctx, rm_annot).into(),
                                        ret_ty.subst(&pi_var, &rhs_ann).eval(ctx, rm_annot).into()
                                    ) //TODO: eval on outside of annot?
                                }
                                else {
                                    unreachable!()
                                }
                            }
                            else {
                                unreachable!()
                            }
                        }
                        _ => Term::App(lhs.eval(ctx, rm_annot).into(), rhs.eval(ctx, rm_annot).into()),
                    }
                }
                else {
                    Term::App(lhs.eval(ctx, rm_annot).into(), rhs.eval(ctx, rm_annot).into())
                }
            }
            Term::Pi(scope) => {
                let ((var, Embed(t1)), t2) = scope.clone().unbind();
                Term::Pi(Scope::new((var, Embed(t1.eval(ctx, rm_annot).into())), t2.eval(ctx, rm_annot).into()))
            }
            Term::Fix(tm) => Term::Fix(tm.eval(ctx, rm_annot).into()),
            Term::Let(scope) => {
                let ((var, Embed(tm)), rest) = scope.clone().unbind();
                Term::Let(Scope::new((var, Embed(tm.eval(ctx, rm_annot).into())), rest.eval(ctx, rm_annot).into()))
            }
            Term::Decl(_) => unimplemented!(),
            Term::Pair(t1, t2) => Term::Pair(t1.eval(ctx, rm_annot).into(), t2.eval(ctx, rm_annot).into()),
            Term::First(tm) => {
                if let Term::Annot(tm, ty) = tm.eval(ctx, rm_annot) {
                    match (*tm.clone(), *ty.clone()) {
                        (Term::Pair(t1, _), Term::Sigma(scope)) => {
                            let ((_, Embed(ty)), _) = scope.unbind();
                            Term::Annot(t1.eval(ctx, rm_annot).into(), ty.eval(ctx, rm_annot).into()) //TODO: eval on outside of annot?
                        }
                        _ => Term::First(tm.eval(ctx, rm_annot).into())
                    }
                } else {
                    Term::First(tm.eval(ctx, rm_annot).into())
                }
            }
            Term::Second(_) => unimplemented!(),
            Term::Sigma(scope) => {
                let ((var, Embed(t1)), t2) = scope.clone().unbind();
                Term::Sigma(Scope::new((var, Embed(t1.eval(ctx, rm_annot).into())), t2.eval(ctx, rm_annot).into()))
            }
            Term::Variant(lbl, tm) => Term::Variant(lbl.to_string(), tm.eval(ctx, rm_annot).into()),
            Term::Case(sm, annot, cases) => {
                let annot = annot.clone().map(|scope| {
                    let (var, body) = scope.unbind();
                    Scope::new(var, body.eval(ctx, rm_annot).into())
                });
                let cases = cases.iter().map(|(lbl, scope)| {
                    let (var, body) = scope.clone().unbind();
                    (lbl.to_string(), Scope::new(var, body.eval(ctx, rm_annot)))
                }).collect();
                Term::Case(sm.eval(ctx, rm_annot).into(), annot, cases)
            }
            Term::Enum(tys) => Term::Enum(tys.iter().map(|(lbl, ty)| (lbl.to_string(), ty.eval(ctx, rm_annot))).collect()),
            Term::Unit => Term::Unit,
            Term::UnitTy => Term::UnitTy,
            Term::Refl => Term::Refl,
            Term::EqElim(c, p, scope) => {
                //if let Term::Annot(tm, ty) = 
                let (var, body) = scope.clone().unbind();
                Term::EqElim(c.eval(ctx, rm_annot).into(), p.eval(ctx, rm_annot).into(), Scope::new(var.clone(), body.eval(ctx, rm_annot).into()))
            }
            Term::EqTy(l, r) => Term::EqTy(l.eval(ctx, rm_annot).into(), r.eval(ctx, rm_annot).into()),
            Term::Fold(tm) => Term::Fold(tm.eval(ctx, rm_annot).into()),
            Term::Unfold(tm) => if let Term::Annot(tm, ty) = tm.eval(ctx, rm_annot) {
                if let Term::Fold(tm) = *tm {
                    Term::Annot(tm, ty) //TODO: eval on outside of annot?
                }
                else {
                    Term::Unfold(tm.eval(ctx, rm_annot).into())
                }
            } else {
                Term::Unfold(tm.eval(ctx, rm_annot).into())
            }
            Term::Rec(scope) => {
                let (a, scope) = scope.clone().unbind();
                let (x, body) = scope.unbind();
                Term::Rec(Scope::new(a.clone(), Scope::new(x.clone(), body.eval(ctx, rm_annot).into())))
            }
        }
    }

    pub fn beq(&self, other: &Self, ctx: &Context) -> bool {
        Term::term_eq(&self.eval(ctx, false), &other.eval(ctx, false))
    }

    pub fn nf(&self, ctx: &Context) -> Self {
        println!("normalizting {}", self);
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
                }
                else {
                    Term::Fix(tm.nf(ctx).into())
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
            Term::First(_) => unimplemented!(),
            Term::Second(_) => unimplemented!(),
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

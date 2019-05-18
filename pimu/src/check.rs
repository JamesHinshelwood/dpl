use crate::ast::{lookup, Term};
use crate::context::Context;
use crate::error::TypeError;
use moniker::{Binder, Embed, FreeVar, Scope, Var};
use std::collections::HashSet;
use std::io::Write;

impl Term {
    pub fn infer_type(&self) -> Result<Self, TypeError> {
        infer_with_ctx(&Context::new(), self)
    }
}

#[allow(clippy::many_single_char_names)]
fn infer_with_ctx(ctx: &Context, term: &Term) -> Result<Term, TypeError> {
    std::io::stdout().flush().unwrap();
    match term {
        Term::Annot(tm, annot) => {
            check_with_ctx(ctx, annot, &Term::Type)?;
            check_with_ctx(ctx, tm, &annot.nf(ctx))?;
            Ok(*annot.clone())
        }
        Term::Type => Ok(Term::Type),
        Term::Var(Var::Free(free_var)) => ctx
            .get_type(free_var)
            .ok_or_else(|| TypeError::VarUnbound(free_var.clone())),
        Term::App(lhs, rhs) => {
            if let Term::Pi(scope) = infer_with_ctx(ctx, lhs)?.nf(ctx) {
                let ((var, Embed(arg_ty)), ret_ty) = scope.unbind();
                check_with_ctx(ctx, rhs, &arg_ty)?;

                Ok(ret_ty.subst(&var, rhs))
            } else {
                Err(TypeError::AppNonLambda(*lhs.clone()))
            }
        }
        Term::Pi(scope) => {
            let ((Binder(var), Embed(arg_ty)), ret_ty) = scope.clone().unbind();
            check_with_ctx(ctx, &arg_ty, &Term::Type)?;
            check_with_ctx(&ctx.with_type(&var, &arg_ty), &ret_ty, &Term::Type)?;

            Ok(Term::Type)
        }
        Term::Let(scope) => {
            let ((Binder(var), Embed(tm)), body) = scope.clone().unbind();
            let ty = infer_with_ctx(ctx, &tm)?;
            infer_with_ctx(
                &ctx.with_type(&var, &ty.nf(ctx)).with_term(&var, &tm),
                &body,
            )
        }
        Term::Decl(scope) => {
            let ((Binder(var), Embed(ty)), body) = scope.clone().unbind();
            check_with_ctx(ctx, &ty, &Term::Type)?;
            infer_with_ctx(&ctx.with_type(&var, &ty), &body)
        }
        Term::Sigma(scope) => {
            let ((Binder(var), Embed(lhs)), rhs) = scope.clone().unbind();
            check_with_ctx(ctx, &lhs, &Term::Type)?;
            check_with_ctx(&ctx.with_type(&var, &lhs), &rhs, &Term::Type)?;

            Ok(Term::Type)
        }
        Term::First(p) => {
            if let Term::Sigma(scope) = infer_with_ctx(ctx, p)?.nf(ctx) {
                let ((_, Embed(ty)), _) = scope.unbind();

                Ok(*ty)
            } else {
                Err(TypeError::FirstNonPair(*p.clone()))
            }
        }
        Term::Second(p) => {
            if let Term::Sigma(scope) = infer_with_ctx(ctx, p)?.nf(ctx) {
                let ((Binder(var), _), ty) = scope.unbind();

                Ok(ty.subst(&var, &Term::First(p.clone())))
            } else {
                Err(TypeError::SecondNonPair(*p.clone()))
            }
        }
        Term::Enum(tys) => {
            let (lbls, tys): (Vec<_>, Vec<_>) = tys.iter().cloned().unzip();

            let mut used_lbls = HashSet::new();
            for lbl in lbls.clone() {
                if !used_lbls.insert(lbl) {
                    return Err(TypeError::EnumLabelsNotUnique(lbls));
                }
            }

            for ty in tys {
                check_with_ctx(ctx, &ty, &Term::Type)?;
            }

            Ok(Term::Type)
        }
        Term::Case(sm, Some(ann), cases) => {
            let (Binder(ann_var), ann_ty) = ann.clone().unbind();
            if let Term::Enum(tys) = infer_with_ctx(ctx, sm)?.nf(ctx) {
                for (lbl, ty) in tys {
                    if let Some(scope) = lookup(&lbl, &cases) {
                        let (Binder(var), body) = scope.clone().unbind();

                        check_with_ctx(
                            &ctx.with_type(&var, &ty).with_term(
                                &ann_var,
                                &Term::Variant(
                                    lbl.to_string(),
                                    Term::Var(Var::Free(var.clone())).into(),
                                ),
                            ),
                            &body,
                            &ann_ty.subst(
                                &ann_var,
                                &Term::Variant(lbl.to_string(), Term::Var(Var::Free(var)).into()),
                            ),
                        )?;
                    } else {
                        return Err(TypeError::CaseBadLabel(term.clone()));
                    }
                }
                Ok(ann_ty.subst(&ann_var, sm))
            } else {
                Err(TypeError::CaseNonSum(term.clone()))
            }
        }
        Term::Unit => Ok(Term::UnitTy),
        Term::UnitTy => Ok(Term::Type),
        Term::UnitElim(scope, unit, body) => {
            let (Binder(var), ty) = scope.clone().unbind();

            check_with_ctx(&ctx.with_type(&var, &Term::UnitTy), &ty, &Term::Type)?;
            check_with_ctx(ctx, unit, &Term::UnitTy)?;
            check_with_ctx(ctx, body, &ty.subst(&var, &Term::Unit))?;

            Ok(ty.subst(&var, unit))
        }
        Term::EqElim(c, p, scope) => {
            let (Binder(var), t) = scope.clone().unbind();

            if let Term::EqTy(l, r, ty) = infer_with_ctx(ctx, p)? {
                let x = FreeVar::fresh_named("x");
                let y = FreeVar::fresh_named("y");
                let q = FreeVar::fresh_unnamed();
                let expected = Term::Pi(Scope::new(
                    (Binder(x.clone()), Embed(ty.clone())),
                    Term::Pi(Scope::new(
                        (Binder(y.clone()), Embed(ty.clone())),
                        Term::Pi(Scope::new(
                            (
                                Binder(q),
                                Embed(
                                    Term::EqTy(
                                        Term::Var(Var::Free(x.clone())).into(),
                                        Term::Var(Var::Free(y.clone())).into(),
                                        ty.clone(),
                                    )
                                    .into(),
                                ),
                            ),
                            Term::Type.into(),
                        ))
                        .into(),
                    ))
                    .into(),
                ));
                check_with_ctx(ctx, &c, &expected)?;

                let var_term: Box<Term> = Term::Var(Var::Free(var.clone())).into();
                check_with_ctx(
                    &ctx.with_type(&var, &ty),
                    &t,
                    &Term::App(
                        Term::App(
                            Term::App(c.clone(), var_term.clone()).into(),
                            var_term.clone(),
                        )
                        .into(),
                        Term::Annot(
                            Term::Refl.into(),
                            Term::EqTy(var_term.clone(), var_term.clone(), ty.clone()).into(),
                        )
                        .into(),
                    ),
                )?;

                Ok(Term::App(
                    Term::App(Term::App(c.clone(), l.clone()).into(), r.clone()).into(),
                    p.clone(),
                ))
            } else {
                Err(TypeError::EqPNotEqTy(*p.clone()))
            }
        }
        Term::EqTy(x, y, ty) => {
            check_with_ctx(ctx, &x, &ty)?;
            check_with_ctx(ctx, &y, &ty)?;

            Ok(Term::Type)
        }
        Term::Unfold(tm) => {
            if let Term::App(rec, ty) = infer_with_ctx(ctx, tm)?.nf(ctx) {
                if let Term::Rec(scope) = *rec.clone() {
                    let (Binder(a), scope) = scope.clone().unbind();
                    let (Binder(x), body) = scope.unbind();

                    Ok(body.subst(&x, &ty).subst(&a, &rec))
                } else {
                    Err(TypeError::UnfoldBadlyFormed(*tm.clone()))
                }
            } else {
                Err(TypeError::UnfoldBadlyFormed(*tm.clone()))
            }
        }
        _ => Err(TypeError::CouldNotInfer(term.clone())),
    }
}

fn check_with_ctx(ctx: &Context, term: &Term, ty: &Term) -> Result<(), TypeError> {
    std::io::stdout().flush().unwrap();
    match (term, &ty.nf(ctx)) {
        (Term::Lam(lam_scope), Term::Pi(pi_scope)) => {
            let ((_, Embed(arg_ty)), ret_ty, Binder(var), body) =
                pi_scope.clone().unbind2(lam_scope.clone());
            check_with_ctx(&ctx.with_type(&var, &arg_ty), &body, &ret_ty)?;

            Ok(())
        }
        (Term::Fix(tm), Term::Pi(pi_scope)) => {
            let (_, rest) = pi_scope.clone().unbind();
            if let Term::Pi(scope) = *rest {
                let ((_, Embed(rec_ty)), _) = scope.clone().unbind();
                if let Term::App(rec, _) = *rec_ty {
                    if let Term::Rec(_) = *rec {
                        let var = FreeVar::fresh_unnamed();
                        let expected_ty = Term::Pi(Scope::new(
                            (Binder(var), Embed(Term::Pi(pi_scope.clone()).into())),
                            Term::Pi(pi_scope.clone()).into(),
                        ));

                        check_with_ctx(ctx, &tm, &expected_ty)?;

                        Ok(())
                    } else {
                        Err(TypeError::FixBadlyFormed(*tm.clone()))
                    }
                } else {
                    Err(TypeError::FixBadlyFormed(*tm.clone()))
                }
            } else {
                Err(TypeError::FixBadlyFormed(*tm.clone()))
            }
        }
        (Term::Pair(l, r), Term::Sigma(scope)) => {
            let ((Binder(var), Embed(lhs)), rhs) = scope.clone().unbind();
            check_with_ctx(ctx, &l, &lhs)?;
            check_with_ctx(ctx, &r, &rhs.subst(&var, &l))?;

            Ok(())
        }
        (Term::Variant(lbl, tm), Term::Enum(lbls)) => {
            if let Some(ty) = lookup(lbl, lbls) {
                check_with_ctx(ctx, tm, &ty)?;

                Ok(())
            } else {
                Err(TypeError::VariantBadLabel(term.clone(), ty.clone()))
            }
        }
        (Term::Case(sm, None, cases), ann) => {
            if let Term::Enum(tys) = infer_with_ctx(ctx, sm)?.nf(ctx) {
                for (lbl, ty) in tys {
                    if let Some(scope) = lookup(&lbl, &cases) {
                        let (Binder(var), body) = scope.clone().unbind();

                        check_with_ctx(&ctx.with_type(&var, &ty), &body, &ann)?;
                    } else {
                        return Err(TypeError::CaseBadLabel(term.clone()));
                    }
                }
                Ok(())
            } else {
                Err(TypeError::CaseNonSum(term.clone()))
            }
        }
        (Term::Refl, Term::EqTy(x, y, _)) => {
            if x.beq(&y, ctx) {
                Ok(())
            } else {
                Err(TypeError::ReflNonEqual(*x.clone(), *y.clone()))
            }
        }
        (Term::Rec(rec_scope), Term::Pi(pi_scope)) => {
            let (Binder(a), rec_scope) = rec_scope.clone().unbind();
            let (Binder(x), rec_body) = rec_scope.unbind();

            let ((_, Embed(x_ty)), pi_body) = pi_scope.clone().unbind();

            check_with_ctx(
                &ctx.with_type(&a, &Term::Pi(pi_scope.clone()))
                    .with_type(&x, &x_ty),
                &rec_body,
                &pi_body,
            )?;

            Ok(())
        }
        (Term::Fold(tm), Term::App(rec, ty)) => {
            if let Term::Rec(scope) = rec.nf(ctx) {
                let (Binder(a), scope) = scope.clone().unbind();
                let (Binder(x), body) = scope.unbind();

                check_with_ctx(ctx, tm, &body.subst(&x, ty).subst(&a, rec))?;

                Ok(())
            } else {
                Err(TypeError::FoldBadlyFormed(*tm.clone()))
            }
        }
        _ => {
            let inf_ty = infer_with_ctx(ctx, term)?;
            if inf_ty.beq(&ty, ctx) {
                Ok(())
            } else {
                Err(TypeError::CouldNotCheck(
                    term.clone(),
                    ty.clone(),
                    inf_ty.clone(),
                ))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::ast::Term;
    use crate::error::TypeError;
    use crate::parser::parse_term;
    use moniker::assert_term_eq;

    #[test]
    fn unit_is_unitty() {
        let term = Term::Unit;
        let ty = term.infer_type().unwrap();

        assert_term_eq!(ty, Term::UnitTy);
    }

    #[test]
    fn type_is_type() {
        let term = Term::Type;
        let ty = term.infer_type().unwrap();

        assert_term_eq!(ty, Term::Type);
    }

    #[test]
    fn lam_without_annot() {
        let term = parse_term("\\x.x").unwrap();
        let ty = term.infer_type().unwrap_err();

        if let TypeError::CouldNotInfer(_) = ty {
        } else {
            panic!("expected CouldNotInfer");
        }
    }

    #[test]
    fn refl_without_annot() {
        let term = Term::Refl;
        let ty = term.infer_type().unwrap_err();

        if let TypeError::CouldNotInfer(_) = ty {
        } else {
            panic!("expected CouldNotInfer");
        }
    }
}

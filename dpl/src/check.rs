use crate::ast::{lookup, Term};
use crate::context::Context;
use crate::error::TypeError;
use moniker::{Binder, Embed, FreeVar, Scope, Var};

impl Term {
    pub fn infer_type(&self) -> Result<Self, TypeError> {
        infer_with_ctx(&Context::new(), self)
    }
}

#[allow(clippy::many_single_char_names)]
fn infer_with_ctx(ctx: &Context, term: &Term) -> Result<Term, TypeError> {
    //println!("{} => ?", term);
    match term {
        Term::Annot(tm, annot) => {
            check_with_ctx(ctx, annot, &Term::Type)?;
            check_with_ctx(ctx, tm, &annot)?;
            Ok(*annot.clone())
        }
        Term::Type => Ok(Term::Type),
        Term::Var(Var::Free(free_var)) => ctx
            .get_type(free_var)
            .ok_or_else(|| TypeError::VarUnbound(free_var.clone())),
        Term::App(lhs, rhs) => {
            if let Term::Pi(scope) = infer_with_ctx(ctx, lhs)?.nf(ctx) {
                let ((var, Embed(arg_ty)), ret_ty) = scope.unbind(); // TODO: Binder<_> ?
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
            infer_with_ctx(&ctx.with_type(&var, &ty).with_term(&var, &tm), &body)
            //infer_with_ctx(&ctx.with_type(&var, &ty), &body.subst(&var, &tm))
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
        Term::Enum(_) => Ok(Term::Type),
        Term::Unit => Ok(Term::UnitTy),
        Term::UnitTy => Ok(Term::Type),
        Term::EqElim(c, p, scope) => {
            let (Binder(var), t) = scope.clone().unbind();

            if let Term::EqTy(l, r) = infer_with_ctx(ctx, p)? {
                let ty = infer_with_ctx(ctx, &l)?;
                let x = FreeVar::fresh_named("x");
                let y = FreeVar::fresh_named("y");
                let q = FreeVar::fresh_unnamed();
                let expected = Term::Pi(Scope::new(
                    (Binder(x.clone()), Embed(ty.clone().into())),
                    Term::Pi(Scope::new(
                        (Binder(y.clone()), Embed(ty.clone().into())),
                        Term::Pi(Scope::new(
                            (
                                Binder(q),
                                Embed(
                                    Term::EqTy(
                                        Term::Var(Var::Free(x.clone())).into(),
                                        Term::Var(Var::Free(y.clone())).into(),
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
                            Term::EqTy(var_term.clone(), var_term.clone()).into(),
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
        Term::EqTy(x, y) => {
            let ty = infer_with_ctx(ctx, &x)?;
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
                    unimplemented!()
                }
            } else {
                unimplemented!()
            }
        }
        // TODO: We could infer the type of (e.g.) Case as long as one of the branches' types can be inferred and the rest checked
        _ => Err(TypeError::CouldNotInfer(term.clone())),
    }
}

fn check_with_ctx(ctx: &Context, term: &Term, ty: &Term) -> Result<(), TypeError> {
    //println!("{} <= {}", term, ty);
    let ty = &ty.nf(ctx);
    match (term, ty) {
        (Term::Lam(lam_scope), Term::Pi(pi_scope)) => {
            let ((_, Embed(arg_ty)), ret_ty, Binder(var), body) =
                pi_scope.clone().unbind2(lam_scope.clone());
            check_with_ctx(&ctx.with_type(&var, &arg_ty), &body, &ret_ty)?;

            Ok(())
        }
        (Term::Fix(tm), ty) => {
            let var = FreeVar::fresh_unnamed();
            let expected_ty = Term::Pi(Scope::new(
                (Binder(var), Embed(ty.clone().into())),
                ty.clone().into(),
            ));
            check_with_ctx(ctx, &tm, &expected_ty)?;

            Ok(())
        }
        (Term::Pair(l, r), Term::Sigma(scope)) => {
            let ((Binder(var), Embed(lhs)), rhs) = scope.clone().unbind();
            check_with_ctx(ctx, &l, &lhs)?;
            check_with_ctx(ctx, &r, &rhs.subst(&var, &l))?; //TODO: Perhaps it would be better to do ctx.with_term(var, l), rather than subst'ing?

            Ok(())
        }
        (Term::LetPair(let_scope), ann) => {
            let (((Binder(x), Binder(y)), Embed(p)), rest) = let_scope.clone().unbind();
            if let Term::Sigma(sigma_scope) = infer_with_ctx(ctx, &p)?.nf(ctx) {
                let ((Binder(x_sigma), Embed(x_ty)), y_ty) = sigma_scope.clone().unbind();
                let y_ty = y_ty.subst(&x_sigma, &Term::Var(Var::Free(x.clone())));
                if let Term::Var(Var::Free(var)) = p.nf(ctx) {
                    check_with_ctx(
                        &ctx.with_type(&x, &x_ty)
                            .with_type(&y, &y_ty)
                            .with_term(&var, &Term::Pair(Term::Var(Var::Free(x.clone())).into(), Term::Var(Var::Free(y)).into())),
                        &rest,
                        ann,
                    )?;
                } else {
                    check_with_ctx(&ctx.with_type(&x, &x_ty).with_type(&y, &y_ty), &rest, ann)?;
                }
                Ok(())
            } else {
                unimplemented!()
            }
        }
        (Term::Variant(l), Term::Enum(ls)) => {
            if ls.contains(l) {
                Ok(())
            } else {
                Err(TypeError::VariantBadLabel(term.clone(), ty.clone()))
            }
        }
        (Term::Case(s, cases), ann) => {
            // TODO: Check domain(cases) = domain(type)
            if let Term::Enum(ls) = infer_with_ctx(ctx, s)?.nf(ctx) {
                for l in ls {
                    if let Some(body) = lookup(&l, cases) {
                        if let Term::Var(Var::Free(var)) = s.nf(ctx) {
                            println!("var is {}\ntm is {}\nin ctx {}\n", var, body.nf(ctx), ctx);
                            check_with_ctx(&ctx.with_term(&var, &Term::Variant(l)), &body, ann)?;
                        } else {
                            check_with_ctx(ctx, &body, ann)?;
                        }
                    } else {
                        return Err(TypeError::CaseBadLabel(term.clone()));
                    }
                }
                Ok(())
            } else {
                Err(TypeError::CaseNonSum(term.clone()))
            }
        }
        (Term::Refl, Term::EqTy(x, y)) => {
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
                unimplemented!("{}", rec)
            }
        }
        _ => {
            let inf_ty = infer_with_ctx(ctx, term)?;
            if inf_ty.beq(&ty, ctx) {
                Ok(())
            } else {
                println!("inferred: {}\n", inf_ty);
                println!("ctx: {}\n", ctx);
                Err(TypeError::CouldNotCheck(term.clone(), ty.clone()))
            }
        }
    }
}

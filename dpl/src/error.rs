use crate::ast::Term;
use crate::print::print_free_var;
use moniker::FreeVar;
use std::fmt;

#[derive(Clone, Debug)]
pub enum TypeError {
    // Infer
    VarUnbound(FreeVar<String>),
    AppNonLambda(Term),
    FirstNonPair(Term),
    SecondNonPair(Term),
    EqPNotEqTy(Term),
    CouldNotInfer(Term),
    // Check
    VariantBadLabel(Term, Term),
    CaseBadLabel(Term),
    CaseNonSum(Term),
    ReflNonEqual(Term, Term),
    CouldNotCheck(Term, Term),
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            TypeError::VarUnbound(var) => write!(f, "The var {} is not bound", print_free_var(var)),
            TypeError::AppNonLambda(lhs) => write!(
                f,
                "Tried to apply a term to {}, which is not a lambda expression",
                lhs
            ),
            TypeError::FirstNonPair(non_pair) => write!(
                f,
                "Tried to take the first element of {}, which is not a pair",
                non_pair
            ),
            TypeError::SecondNonPair(non_pair) => write!(
                f,
                "Tried to take the second element of {}, which is not a pair",
                non_pair
            ),
            TypeError::EqPNotEqTy(p) => write!(
                f,
                "{} in an equality elimination is not an equality type.",
                p
            ),
            TypeError::CouldNotInfer(tm) => write!(
                f,
                "Could not infer the type of {}. Try adding an annotation",
                tm
            ),
            TypeError::VariantBadLabel(variant, ty) => write!(
                f,
                "The variant {} is not a valid instance of the sum type {}",
                variant, ty
            ),
            TypeError::CaseBadLabel(tm) => {
                write!(f, "Case {} contains a branch with an invalid label", tm)
            }
            TypeError::CaseNonSum(non_sum) => {
                write!(f, "Tried to case split a {}, which is not a sum", non_sum)
            }
            TypeError::ReflNonEqual(x, y) => write!(
                f,
                "Tried to construct a refl of non-equal terms, {} and {}",
                x, y
            ),
            TypeError::CouldNotCheck(tm, ty) => {
                write!(f, "Could not check {} was of type {}", tm, ty)
            }
        }
    }
}

module

public import Flapjack.Compiler.Inference.Infer.Core
public import Flapjack.Compiler.Inference.Infer.HOLState
public import Flapjack.Compiler.Inference.Infer.Operations
public import Flapjack.Compiler.Inference.Unify.Source.Continuation
public import Flapjack.Compiler.Inference.Unify.Walkstar.Computational

@[expose] public section

/-! Relating executable constraints to source-shaped state and diagnostics. -/
namespace Flapjack.Compiler.Inference.Infer.Constraint
open Flapjack.Compiler.Inference.Unify Flapjack.Compiler.Inference.Infer.HOLState
  Flapjack.Compiler.Inference.Infer.Operations Flapjack.Compiler.Inference.InferTDisplay
  Flapjack.Translator.Monadic.MonadBase Flapjack.HOL.Transfer.Fmsp
  Flapjack.Basis.Pure.MlString Flapjack.Misc.Location

/-- The source error message after normalizing both sides of a failed
    constraint. The executable stores the normalized types for later rendering. -/
def mismatchMessage (l : LocErrInfo) (a b : InferT) : MlString :=
  MlString.concat [ofString "Type mismatch between ", inferTypeToString l.err a,
    ofString " and ", inferTypeToString l.err b]

/-- Source-shaped constraint operation. This remains untagged while the
    unifier's and normalizer's choices outside well-formedness are unresolved. -/
noncomputable def addConstraintModel (l : LocErrInfo) (a b : InferT) :
    M InferState Unit (Option Locs × MlString) := fun s =>
  match tUnifyModel s.subst a b with
  | none => (.failure (l.loc, mismatchMessage l (tWalkstar s.subst a) (tWalkstar s.subst b)), s)
  | some subst => (.success (), { s with subst })

/-- Source-shaped list constraint operation. It is not tagged as HOL's
    `add_constraints_def` because its single-constraint operation uses the
    unreviewed source unifier and normalizer choices on ill-formed maps. -/
noncomputable def addConstraintsModel (l : LocErrInfo) : List InferT → List InferT →
    M InferState Unit (Option Locs × MlString)
  | [], [] => ret ()
  | a :: as, b :: bs => bind (addConstraintModel l a b) (fun _ =>
      bind (addConstraintsModel l as bs) (fun _ => ret ()))
  | _, _ => failwith l (ofString "Internal error: Bad call to add_constraints")

/-- Unfolding of the executable constraint step for the correspondence proof. -/
private theorem constrainApply (fuel : Nat) (a b : InferT) (s : Infer.State) :
    Core.constrain fuel a b s =
      match unifyPartial s.subst a b with
      | none => (.error .exhausted, s)
      | some none =>
        match walkStar s.subst a, walkStar s.subst b with
        | some left, some right => (.error (.typeMismatch left right), s)
        | _, _ => (.error .mismatch, s)
      | some (some subst) => (.ok (), { s with subst }) := by
  rfl

/-- On well-formed executable substitutions the partial constraint executor
    agrees with the source-shaped unifier and retains the types needed for the
    source diagnostic. Rendering the complete executable error is separate. -/
theorem constrainCorresponds (fuel : Nat) (a b : InferT) (s : Infer.State)
    (l : LocErrInfo) (hw : cwfs s.subst) :
    match cunifyModel s.subst a b with
    | none =>
      Core.constrain fuel a b s = (.error (.typeMismatch (tWalkstar (sp2fm s.subst) a) (tWalkstar (sp2fm s.subst) b)), s) ∧
      addConstraintModel l a b (ofExecutable s) =
        (.failure (l.loc, mismatchMessage l (tWalkstar (sp2fm s.subst) a) (tWalkstar (sp2fm s.subst) b)), ofExecutable s)
    | some subst =>
      Core.constrain fuel a b s = (.ok (), { s with subst }) ∧
      addConstraintModel l a b (ofExecutable s) = (.success (), ofExecutable { s with subst }) := by
  have hu := unifyPartialMatchesSource s.subst a b hw
  have ha : walkStar s.subst a = some (tWalkstar (sp2fm s.subst) a) := by
    simp [walkStar, walkStarListCorrect s.subst hw]
  have hb : walkStar s.subst b = some (tWalkstar (sp2fm s.subst) b) := by
    simp [walkStar, walkStarListCorrect s.subst hw]
  have mapped := cunifyModelMap s.subst a b
  cases found : cunifyModel s.subst a b with
  | none =>
    simp [found] at hu mapped
    simp [constrainApply, hu, ha, hb, addConstraintModel, ofExecutable, ← mapped]
  | some subst =>
    simp [found] at hu mapped
    simp [constrainApply, hu, addConstraintModel, ofExecutable, ← mapped]

end Flapjack.Compiler.Inference.Infer.Constraint

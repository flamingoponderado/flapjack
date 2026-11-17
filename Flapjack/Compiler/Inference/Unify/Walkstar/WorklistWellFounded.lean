module

public import Flapjack.Compiler.Inference.Unify.Walkstar.WorklistMeasure
public import Flapjack.Compiler.Inference.Unify.ComputationalWf
public import Flapjack.HOL.Unification.Walkstar.WellFounded
import Mathlib.Order.RelClasses

@[expose] public section

/-! The source normalization worklist's lexicographic termination order. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- A parameterized form of the source relation. The source computes its
    finite map inside the definition; this form exposes the reviewed producer. -/
def starWorklistOrder (subst : HolFiniteMapExact Nat (Term Atom))
    (child parent : Bool × List InferT × List KclKont) : Prop :=
  let childBag := starWorkbag child.1 child.2.1 child.2.2
  let parentBag := starWorkbag parent.1 parent.2.1 parent.2.2
  Relation.TransGen (bagMultisetStep (fun a b => walkstarR subst (encodeInferT a) (encodeInferT b)))
      childBag parentBag ∨
    (childBag = parentBag ∧
      (child.2.2.length < parent.2.2.length ∨
        (child.2.2.length = parent.2.2.length ∧
          ((child.2.2.filter isConsK).length < (parent.2.2.filter isConsK).length ∨
            ((child.2.2.filter isConsK).length = (parent.2.2.filter isConsK).length ∧
              (if child.1 then 0 else 1) < (if parent.1 then 0 else 1))))))

/-- The original relation is expanded through its map parameter so the
    canonical `sp2fm` observation is explicit in the theorem type. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "WF_kcwalkstarwlR"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem wfKcwalkstarwlRModel (s : Spt InferT) (hw : cwfs s) :
    WellFounded (starWorklistOrder ((sp2fm s).map2 (fun p => encodeInferT p.2))) := by
  have hsubst : wfs ((sp2fm s).map2 (fun p => encodeInferT p.2)) := by
    change WellFounded (cvwalkR s)
    exact wfCvwalkR s 0 hw
  have termWf := InvImage.wf encodeInferT (walkstarThWF _ hsubst)
  have bagWf := (wfBagMultisetStep _ termWf).transGen
  let rank (state : Bool × List InferT × List KclKont) :=
    (starWorkbag state.1 state.2.1 state.2.2,
      (state.2.2.length, ((state.2.2.filter isConsK).length, if state.1 then 0 else 1)))
  have lexWf := bagWf.prod_lex (Nat.lt_wfRel.wf.prod_lex
    (Nat.lt_wfRel.wf.prod_lex Nat.lt_wfRel.wf))
  apply Subrelation.wf _ (InvImage.wf rank lexWf)
  intro child parent h
  rcases h with h | ⟨bagEq, h⟩
  · exact Prod.Lex.left _ _ h
  · change Prod.Lex _ _ (rank child) (rank parent)
    dsimp only [rank]
    rw [bagEq]
    apply Prod.Lex.right
    rcases h with h | ⟨lenEq, h⟩
    · exact Prod.Lex.left _ _ h
    · rw [lenEq]
      apply Prod.Lex.right
      rcases h with h | ⟨filterEq, h⟩
      · exact Prod.Lex.left _ _ h
      · rw [filterEq]
        exact Prod.Lex.right _ h

end Flapjack.Compiler.Inference.Unify

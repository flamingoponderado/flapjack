module

public import Flapjack.Compiler.Inference.Unify.Occurs.WorklistDecrease
public import Flapjack.HOL.Unification.Walkstar.WellFounded
import Mathlib.Order.RelClasses

@[expose] public section

/-! Well-foundedness of the original occurs-check worklist measure. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- The original relation is unfolded to expose its finite-map observation. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "WF_kcocwlR"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem wfKcocwlRModel (s : Spt InferT) (n : Nat) (hw : cwfs s) :
    WellFounded (fun child parent : List (List InferT) =>
      bagMultisetStep (walkstarR (sp2fm (sptMap encodeInferT s)))
          (bagOfList (child.flatten.map encodeInferT)) (bagOfList (parent.flatten.map encodeInferT)) ∨
        (bagOfList (child.flatten.map encodeInferT) = bagOfList (parent.flatten.map encodeInferT) ∧
          child.length < parent.length)) := by
  have _ := n
  have hwf : wfs (sp2fm (sptMap encodeInferT s)) := hw.1
  have bags := wfBagMultisetStep _ (walkstarThWF _ hwf)
  apply Subrelation.wf _ (InvImage.wf
    (fun work : List (List InferT) => (bagOfList (work.flatten.map encodeInferT), work.length))
    (bags.prod_lex Nat.lt_wfRel.wf))
  intro child parent h
  rcases h with h | ⟨eq, lt⟩
  · exact Prod.Lex.left _ _ h
  · change Prod.Lex (bagMultisetStep (walkstarR (sp2fm (sptMap encodeInferT s)))) (· < ·)
      (bagOfList (child.flatten.map encodeInferT), child.length)
      (bagOfList (parent.flatten.map encodeInferT), parent.length)
    rw [eq]
    exact Prod.Lex.right _ lt

end Flapjack.Compiler.Inference.Unify

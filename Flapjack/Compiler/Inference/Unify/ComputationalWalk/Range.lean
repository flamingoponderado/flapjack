module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk.Total
public import Flapjack.HOL.Unification.TcallUnif.WalkRange

@[expose] public section

/-! Variable bounds for the source-shaped computational walkers. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

@[hol "cakeml/compiler/inference/unifyScript.sml" "tcwalk_rangevars"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem tcwalkRangeVarsModel (s : Spt InferT) (t u : InferT)
    (h : cwfs s ∧ tcwalkModel s t = u) :
    Set.Subset (vars (encodeInferT u))
      (Set.union (rangeVars ((sp2fm s).map2 (fun p => encodeInferT p.2))) (vars (encodeInferT t))) := by
  have hw : tWfs (sp2fm s) := wfCvwalkR s 0 h.1
  have he : walk ((sp2fm s).map2 (fun p => encodeInferT p.2)) (encodeInferT t) = encodeInferT u := by
    rw [encodeWalk (sp2fm s) hw t]
    have correct := tcwalkCorrectModel s t h.1
    change tWalk (sp2fm s) t = tcwalkModel s t at correct
    rw [correct, h.2]
  exact walkRangeVars _ _ _ ⟨hw, he⟩

@[hol "cakeml/compiler/inference/unifyScript.sml" "tcvwalk_substvars"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem tcvwalkSubstVarsModel (s : Spt InferT) (v : Nat) (t : InferT)
    (h : cwfs s ∧ tcvwalkModel s v = t) :
    (t = .uvar v ∧ ¬ sptDomain s v) ∨
      Set.Subset (vars (encodeInferT t)) (substVars ((sp2fm s).map2 (fun p => encodeInferT p.2))) := by
  have hw : tWfs (sp2fm s) := wfCvwalkR s v h.1
  have he : vwalk ((sp2fm s).map2 (fun p => encodeInferT p.2)) v = encodeInferT t := by
    rw [encodeVwalk (sp2fm s) hw v]
    have correct := tcvwalkCorrectModel s v h.1
    change tVwalk (sp2fm s) v = tcvwalkModel s v at correct
    rw [correct, h.2]
  rcases vwalkRangeVars _ v _ ⟨hw, he⟩ with ⟨eq, absent⟩ | range
  · left
    constructor
    · have decoded := congrArg decodeInferT eq
      simpa [decodeLeftInverse, decodeInferT] using decoded
    · intro present
      obtain ⟨value, found⟩ := (sptDomain_iff_lookup s v).mp present
      apply absent
      change ((sp2fm s).map2 (fun p => encodeInferT p.2)).lookup v ≠ none
      simp [HolFiniteMapExact.lookup_map2, sp2fm, found]
  · right
    intro key member
    exact Or.inr (range member)

end Flapjack.Compiler.Inference.Unify

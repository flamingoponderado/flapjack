module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk.Total
public import Flapjack.Compiler.Inference.Unify.Subterm.Walkstar
public import Flapjack.HOL.Unification.Walkstar.Decrease

@[expose] public section

/-! The source walker's application arguments decrease in the walkstar order. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

@[hol "cakeml/compiler/inference/unifyScript.sml" "walkstar_opth"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem walkstarOpthModel (s : Spt InferT) (i i0 : InferT) (is : List InferT) (nm : Nat)
    (h : cwfs s ∧ tcwalkModel s i = .app is nm ∧ i0 ∈ is) :
    walkstarR (sp2fm (sptMap encodeInferT s)) (encodeInferT i0) (encodeInferT i) := by
  have hm : sp2fm (sptMap encodeInferT s) =
      (sp2fm s).map2 (fun p => encodeInferT p.2) := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    exact sptLookup_sptMap encodeInferT s key
  have hw : tWfs (sp2fm s) := by
    change wfs ((sp2fm s).map2 (fun p => encodeInferT p.2))
    rw [← hm]
    exact h.1.1
  have hi : tWalk (sp2fm s) i = .app is nm := by
    have correct := tcwalkCorrectModel s i h.1
    change tWalk (sp2fm s) i = tcwalkModel s i at correct
    exact correct.trans h.2.1
  have hwalk : walk (sp2fm (sptMap encodeInferT s)) (encodeInferT i) =
      .pair (.const .tappTag) (.pair (.const (.tcTag nm)) (encodeInferTs is)) := by
    simpa [← hm, hi, encodeInferT] using encodeWalk (sp2fm s) hw i
  have part : subterm (encodeInferT i0) (.pair (.const (.tcTag nm)) (encodeInferTs is)) :=
    (memSubtermEncode i0 is h.2.2).tail (Or.inr ⟨_, rfl⟩)
  exact walkstarRTrans _ _ _ _ ⟨subtermWalkstarR _ _ _ part,
    walkstarTh2 _ h.1.1 _ _ _ hwalk⟩

end Flapjack.Compiler.Inference.Unify

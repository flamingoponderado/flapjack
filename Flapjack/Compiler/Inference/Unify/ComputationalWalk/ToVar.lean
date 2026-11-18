module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk
public import Flapjack.Compiler.Inference.Unify.ComputationalWalk.Total
public import Flapjack.Compiler.Inference.Unify.Walk.ToVar

@[expose] public section

/-! Freshness of variables returned by the executed inference walker. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- A variable returned by the total walker is fresh in the substitution,
    and the walk started from a variable. -/
@[hol "cakeml/compiler/inference/unifyScript.sml" "tcwalk_EQ_Infer_Tuvar"]
theorem tcwalkEqInferTuvarModel (s : Spt InferT) (t : InferT) (v : Nat)
    (h : cwfs s ∧ tcwalkModel s t = .uvar v) :
    ¬ sptDomain s v ∧ ∃ u, t = .uvar u := by
  obtain ⟨hw, result⟩ := h
  have eq : cwalkModel s t = .uvar v := (tcwalkCorrectModel s t hw).trans result
  cases t with
  | varDb n => simp [cwalkThm s (.varDb n) hw] at eq
  | app l n => simp [cwalkThm s (.app l n) hw] at eq
  | uvar u =>
    constructor
    · have hv : tVwalk (sp2fm s) u = .uvar v := by
        simpa [cwalkThm s (.uvar u) hw, cvwalkModel] using eq
      have hws : tWfs (sp2fm s) := by
        change WellFounded (vR ((sp2fm s).map2 (fun p => encodeInferT p.2)))
        exact wfCvwalkR s u hw
      have absent := tVwalkToVar (sp2fm s) hws u v hv
      intro present
      obtain ⟨value, found⟩ := (sptDomain_iff_lookup s v).mp present
      apply absent
      change sptLookup v s ≠ none
      simp [found]
    · exact ⟨u, rfl⟩

end Flapjack.Compiler.Inference.Unify

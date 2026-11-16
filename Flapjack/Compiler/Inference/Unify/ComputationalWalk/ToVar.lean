module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk
public import Flapjack.Compiler.Inference.Unify.Walk.ToVar

@[expose] public section

/-! Freshness of variables returned by the executed inference walker. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- If the executed walker actually returns a variable on a well-formed
    substitution, that variable is absent from the tree and its input was a
    variable. This raw `Option` result supports the unifier's update proof;
    it is not tagged as HOL's total `tcwalk_EQ_Infer_Tuvar` theorem. -/
theorem walkExecutableToVar (s : Spt InferT) (t : InferT) (v : Nat)
    (h : cwfs s ∧ walkExecutable s t = some (.uvar v)) :
    ¬ sptDomain s v ∧ ∃ u, t = .uvar u := by
  obtain ⟨hw, result⟩ := h
  have model := walkExecutableCorrect s hw t
  rw [result] at model
  have eq : cwalkModel s t = .uvar v := (Option.some.inj model).symm
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

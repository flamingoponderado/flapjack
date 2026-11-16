module

public import Flapjack.Compiler.Inference.Unify.ComputationalWalk
public import Flapjack.Compiler.Inference.Unify.Walk.ToVar

@[expose] public section

/-! Correctness of the computational walkers on well-formed substitutions. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

/-- A total proof model for the executed partial walker. The default is used
    only when the partial computation has no result; no correspondence with
    HOL's unspecified tail-recursion result is claimed outside `cwfs`. -/
def tcvwalkModel (s : Spt InferT) (n : Nat) : InferT :=
  (cvwalkPartial s n).getD (.varDb 0)

/-- The corresponding type walker; it inherits `tcvwalkModel`'s explicit
    off-`cwfs` limitation. -/
def tcwalkModel (s : Spt InferT) : InferT → InferT
  | .varDb c => .varDb c
  | .app l n => .app l n
  | .uvar v => tcvwalkModel s v

@[hol "cakeml/compiler/inference/unifyScript.sml" "tcvwalk_correct"]
theorem tcvwalkCorrect (s : Spt InferT) : ∀ x, cwfs s → cvwalkModel s x = tcvwalkModel s x := by
  intro x hw
  simp [tcvwalkModel, cvwalkPartialCorrect s hw x]

@[hol "cakeml/compiler/inference/unifyScript.sml" "tcwalk_correct"]
theorem tcwalkCorrect (s : Spt InferT) (it : InferT) (hw : cwfs s) :
    cwalkModel s it = tcwalkModel s it := by
  rw [cwalkThm s it hw]
  cases it with
  | varDb c => rfl
  | app l n => rfl
  | uvar v => exact tcvwalkCorrect s v hw

@[hol "cakeml/compiler/inference/unifyScript.sml" "tcwalk_EQ_Infer_Tuvar"]
theorem tcwalkEqInferTuvar (s : Spt InferT) (t : InferT) (v : Nat)
    (h : cwfs s ∧ tcwalkModel s t = .uvar v) :
    ¬ sptDomain s v ∧ ∃ u, t = .uvar u := by
  obtain ⟨hw, eq⟩ := h
  rw [← tcwalkCorrect s t hw] at eq
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

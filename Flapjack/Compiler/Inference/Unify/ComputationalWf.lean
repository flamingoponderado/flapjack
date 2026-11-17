module

public import Flapjack.Compiler.Inference.Unify
public import Flapjack.Compiler.Inference.Unify.Encoding
public import Flapjack.HOL.Unification.Rmfmap
public import Flapjack.Misc.Sptree.Map
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

/-! Original well-formedness and decrease relation for the computational walker. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification Flapjack.HOL.Transfer.Fmsp

@[hol "cakeml/compiler/inference/unifyScript.sml" "cwfs_def"]
def cwfs (s : Spt InferT) : Prop :=
  swfs (sptMap encodeInferT s) ∧ sptWf s = true

@[hol "cakeml/compiler/inference/unifyScript.sml" "cvwalk_preserves_precond"]
theorem cvwalkPreservesPrecond (s : Spt InferT) : ∀ x y,
    (fun _ : Nat => cwfs s) x ∧ cvwalkCode s x = .inl y →
      (fun _ : Nat => cwfs s) y := by
  intro x y h
  exact h.1

@[hol "cakeml/compiler/inference/unifyScript.sml" "cvwalkR_def"]
def cvwalkR (s : Spt InferT) : Nat → Nat → Prop :=
  vR ((sp2fm s).map2 (fun p => encodeInferT p.2))

@[hol "cakeml/compiler/inference/unifyScript.sml" "cvwalk_ensures_decrease"]
theorem cvwalkEnsuresDecrease (s : Spt InferT) : ∀ x y,
    (fun _ : Nat => cwfs s) x ∧ cvwalkCode s x = .inl y → cvwalkR s y x := by
  intro x y h
  cases found : sptLookup x s with
  | none => simp [cvwalkCode, found] at h
  | some t =>
    cases t with
    | varDb n => simp [cvwalkCode, found] at h
    | app ts tc => simp [cvwalkCode, found] at h
    | uvar u =>
      have eq : u = y := by simpa [cvwalkCode, found] using h.2
      subst y
      simp [cvwalkR, vR, HolFiniteMapExact.lookup_map2, sp2fm, found, encodeInferT, vars]

@[hol "cakeml/compiler/inference/unifyScript.sml" "WF_cvwalkR"]
theorem wfCvwalkR {α : Type} (s : Spt InferT) : ∀ x : α,
    (fun _ : α => cwfs s) x → WellFounded (cvwalkR s) := by
  intro x h
  have heq : sp2fm (sptMap encodeInferT s) =
      (sp2fm s).map2 (fun p => encodeInferT p.2) := by
    apply HolFiniteMapExact.ext_lookup
    intro key
    exact sptLookup_sptMap encodeInferT s key
  change wfs (sp2fm (sptMap encodeInferT s)) ∧ sptWf s = true at h
  change WellFounded (vR ((sp2fm s).map2 (fun p => encodeInferT p.2)))
  rw [← heq]
  exact h.1

end Flapjack.Compiler.Inference.Unify

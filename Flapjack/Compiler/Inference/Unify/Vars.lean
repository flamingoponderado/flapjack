module

public import Flapjack.Compiler.Inference.Unify.Substitution
public import Mathlib.Data.Set.Lattice

@[expose] public section

namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

/-- Relate the encoded list traversal to the variables of its members. -/
private theorem encodedListVars (ts : List InferT) (v : Nat) :
    vars (encodeInferTs ts) v ↔ ∃ t ∈ ts, tVars t v := by
  induction ts with
  | nil => simp [encodeInferTs, vars]
  | cons t ts ih => simp [encodeInferTs, vars, tVars, ih]

@[hol "cakeml/compiler/inference/unifyScript.sml" "t_vars_eqn"]
theorem tVarsEqn :
    (∀ x, tVars (.varDb x) = (∅ : Set Nat)) ∧
    (∀ (ts : List InferT) tc,
      tVars (.app ts tc) = Set.sUnion (Set.image tVars (fun t => t ∈ ts))) ∧
    (∀ u, tVars (.uvar u) = ({u} : Set Nat)) := by
  constructor
  · intro x
    apply Set.ext
    intro v
    simp only [tVars, encodeInferT, vars]
    change False ↔ False
    rfl
  constructor
  · intro ts tc
    apply Set.ext
    intro v
    change vars (encodeInferT (.app ts tc)) v ↔ ∃ p : Nat → Prop,
      (∃ t, t ∈ ts ∧ tVars t = p) ∧ p v
    simp only [encodeInferT, vars, false_or, encodedListVars]
    constructor
    · rintro ⟨t, ht, hv⟩
      exact ⟨tVars t, ⟨t, ht, rfl⟩, hv⟩
    · rintro ⟨_, ⟨t, ht, rfl⟩, hv⟩
      exact ⟨t, ht, hv⟩
  · intro u
    apply Set.ext
    intro v
    simp only [tVars, encodeInferT, vars]
    change (v = u) ↔ (v = u)
    rfl

end Flapjack.Compiler.Inference.Unify

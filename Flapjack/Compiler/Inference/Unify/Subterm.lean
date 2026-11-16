module

public import Flapjack.Compiler.Inference.Unify.Encoding
public import Mathlib.Logic.Relation
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! The structural subterm order used in the unifier termination proof. -/
namespace Flapjack.Compiler.Inference.Unify
open Flapjack.HOL.Unification

@[hol "cakeml/compiler/inference/unifyScript.sml" "subterm_def"]
def subterm {α : Type} : Term α → Term α → Prop :=
  Relation.TransGen (fun a b => (∃ t, b = .pair a t) ∨ (∃ t, b = .pair t a))

@[hol "cakeml/compiler/inference/unifyScript.sml" "subterm_pair_count"]
theorem subtermPairCount {α : Type} (t u : Term α) (h : subterm t u) :
    pairCount t < pairCount u := by
  induction h with
  | single edge =>
    rcases edge with ⟨other, rfl⟩ | ⟨other, rfl⟩ <;> simp [pairCount] <;> omega
  | tail path edge ih =>
    rcases edge with ⟨other, rfl⟩ | ⟨other, rfl⟩ <;> simp [pairCount] <;> omega

@[hol "cakeml/compiler/inference/unifyScript.sml" "subterm_REFL"]
theorem subtermRefl {α : Type} (t : Term α) : ¬ subterm t t := by
  intro h
  exact Nat.lt_irrefl _ (subtermPairCount t t h)

@[hol "cakeml/compiler/inference/unifyScript.sml" "subterm_TRANS"]
theorem subtermTrans {α : Type} (t u v : Term α)
    (h : subterm t u ∧ subterm u v) : subterm t v := h.1.trans h.2

@[hol "cakeml/compiler/inference/unifyScript.sml" "subterm_thm"]
theorem subtermThm {α : Type} (t u v : Term α) (vnm : Nat) (c : α) :
    (subterm t (.pair u v) ↔ t = u ∨ t = v ∨ subterm t u ∨ subterm t v) ∧
    (subterm t (.var vnm) ↔ False) ∧
    (subterm t (.const c) ↔ False) := by
  constructor
  · constructor
    · intro h
      obtain ⟨mid, path, edge⟩ := Relation.TransGen.tail'_iff.mp h
      rcases edge with ⟨other, eq⟩ | ⟨other, eq⟩
      · cases eq
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with eq | path
        · exact Or.inl eq.symm
        · exact Or.inr (Or.inr (Or.inl path))
      · cases eq
        rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with eq | path
        · exact Or.inr (Or.inl eq.symm)
        · exact Or.inr (Or.inr (Or.inr path))
    · rintro (rfl | rfl | h | h)
      · exact Relation.TransGen.single (Or.inl ⟨_, rfl⟩)
      · exact Relation.TransGen.single (Or.inr ⟨_, rfl⟩)
      · exact h.tail (Or.inl ⟨_, rfl⟩)
      · exact h.tail (Or.inr ⟨_, rfl⟩)
  · constructor <;> constructor
    · intro h
      obtain ⟨_, _, edge⟩ := Relation.TransGen.tail'_iff.mp h
      rcases edge with ⟨_, eq⟩ | ⟨_, eq⟩ <;> cases eq
    · exact False.elim
    · intro h
      obtain ⟨_, _, edge⟩ := Relation.TransGen.tail'_iff.mp h
      rcases edge with ⟨_, eq⟩ | ⟨_, eq⟩ <;> cases eq
    · exact False.elim

@[hol "cakeml/compiler/inference/unifyScript.sml" "MEM_subterm_encode"]
theorem memSubtermEncode (i : InferT) (is : List InferT) (h : i ∈ is) :
    subterm (encodeInferT i) (encodeInferTs is) := by
  induction is with
  | nil => simp at h
  | cons head tail ih =>
    simp only [List.mem_cons] at h
    simp only [encodeInferTs]
    rcases h with rfl | h
    · exact Relation.TransGen.single (Or.inl ⟨_, rfl⟩)
    · exact (ih h).tail (Or.inr ⟨_, rfl⟩)

end Flapjack.Compiler.Inference.Unify

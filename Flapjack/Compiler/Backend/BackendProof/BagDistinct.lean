module

public import Flapjack.Misc.Bag.Image
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.ByContra

@[expose] public section

/-! backendProofScript.sml 1094-1118: `BAG_IMAGE SUC` preserves distinctness
of bags of numbers. -/
namespace Flapjack.Compiler.Backend.BackendProof

open Flapjack

/-- Invariant of the HOL bag cardinality relation (Flapjack infrastructure):
cardinality zero is exactly the empty bag, and cardinality at least two
needs two occurrences. -/
private theorem bagCardRel_inv {α : Type} (b : Bag α) (n : Nat) (h : bagCardRel b n) :
    (n = 0 ↔ ∀ e, b e = 0) ∧
      (2 ≤ n → ∃ e1 e2, (e1 ≠ e2 ∧ 1 ≤ b e1 ∧ 1 ≤ b e2) ∨ 2 ≤ b e1) := by
  classical
  apply h (fun b n => (n = 0 ↔ ∀ e, b e = 0) ∧
    (2 ≤ n → ∃ e1 e2, (e1 ≠ e2 ∧ 1 ≤ b e1 ∧ 1 ≤ b e2) ∨ 2 ≤ b e1))
  refine ⟨⟨⟨fun _ _ => rfl, fun _ => rfl⟩, fun h => absurd h (by omega)⟩, ?_⟩
  intro b n ⟨h0, h2⟩ e
  refine ⟨⟨fun h => absurd h (by omega), fun h => ?_⟩, fun hn => ?_⟩
  · have := h e
    simp [bagInsert] at this
  · have hne : n ≠ 0 := by omega
    have : ¬ ∀ e, b e = 0 := fun hz => hne (h0.2 hz)
    push Not at this
    obtain ⟨e1, he1⟩ := this
    by_cases hx : e1 = e
    · subst hx
      exact ⟨e1, e1, .inr (by simp [bagInsert]; omega)⟩
    · refine ⟨e1, e, .inl ⟨hx, ?_, ?_⟩⟩
      · simp [bagInsert, hx]; omega
      · simp [bagInsert]

/-- A finite bag with at most one occurrence of at most one element has
HOL cardinality at most one (Flapjack infrastructure). -/
private theorem holBagCard_le_one {α : Type} (b : Bag α) (hf : finiteBag b)
    (h : ∀ e1 e2, 1 ≤ b e1 → 1 ≤ b e2 → e1 = e2) (h1 : ∀ e, b e ≤ 1) :
    holBagCard b ≤ 1 := by
  have inv := bagCardRel_inv b _ (holBagCard_spec b hf)
  by_contra hc
  obtain ⟨e1, e2, (⟨hne, a, c⟩ | d)⟩ := inv.2 (by omega)
  · exact hne (h e1 e2 a c)
  · have := h1 e1; omega

/-- `BAG_IMAGE SUC` of a distinct bag has multiplicities at most one
(Flapjack infrastructure). -/
private theorem bagImage_succ_le_one (s : Bag Nat) (hs : bagAllDistinct s) (e : Nat) :
    bagImage Nat.succ s e ≤ 1 := by
  classical
  simp only [bagImage]
  split_ifs with hf
  · apply holBagCard_le_one _ hf
    · intro e1 e2 h1 h2
      simp only [bagFilter] at h1 h2
      split_ifs at h1 h2 with a b <;> omega
    · intro e'
      simp only [bagFilter]
      split_ifs
      · exact hs e'
      · omega
  · exact Nat.le_refl 1

/-- Exact HOL `BAG_ALL_DISTINCT_BAG_IMAGE_SUC` (`backendProofScript.sml:1094-1111`,
`[local]`). -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "BAG_ALL_DISTINCT_BAG_IMAGE_SUC"]
theorem bagAllDistinct_bagImage_succ (s : Bag Nat) :
    bagAllDistinct s → bagAllDistinct (bagImage Nat.succ s) :=
  fun hs e => bagImage_succ_le_one s hs e

/-- Exact HOL `BAG_ALL_DISTINCT_BAG_IMAGE_SUC'` (`backendProofScript.sml:1113-1118`,
`[local]`). `{|0|}` is `bagInsert 0 emptyBag` and `⊎` is `bagUnion`. -/
@[hol "cakeml/compiler/backend/proofs/backendProofScript.sml" "BAG_ALL_DISTINCT_BAG_IMAGE_SUC'"]
theorem bagAllDistinct_bagImage_succ' (s : Bag Nat) :
    bagAllDistinct s → bagAllDistinct (bagUnion (bagInsert 0 emptyBag) (bagImage Nat.succ s)) := by
  classical
  intro hs e
  simp only [bagUnion]
  by_cases he : e = 0
  · subst he
    have h0 : bagImage Nat.succ s 0 = 0 := by
      have hz : bagFilter (fun e₀ => Nat.succ e₀ = 0) s = emptyBag := by
        funext x; simp [bagFilter, emptyBag]
      simp only [bagImage, hz]
      rw [if_pos (finiteEmptyBag)]
      have inv := bagCardRel_inv _ _ (holBagCard_spec (emptyBag : Bag Nat) finiteEmptyBag)
      exact inv.1.2 (fun _ => rfl)
    simp [bagInsert, emptyBag, h0]
  · have := bagImage_succ_le_one s hs e
    simp [bagInsert, emptyBag, he, this]

end Flapjack.Compiler.Backend.BackendProof

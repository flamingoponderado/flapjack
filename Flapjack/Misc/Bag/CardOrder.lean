import Flapjack.Misc.Bag.Card
import Flapjack.Misc.Bag.SubBag
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Finite.Basic

open scoped BigOperators
/-! Cardinality of a sub-bag. -/
namespace Flapjack

/-- Flapjack infrastructure: a finite HOL bag has finite nonzero support. -/
private theorem supportFinite {α : Type} (b : Bag α) (hb : finiteBag b) :
    {x | b x ≠ 0}.Finite := by
  classical
  apply hb (fun b => {x | b x ≠ 0}.Finite)
  constructor
  · simp [emptyBag]
  · intro b h e
    apply (h.insert e).subset
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx
    simp only [Set.mem_insert_iff, Set.mem_ofPred_eq]
    by_cases he : x = e
    · exact Or.inl he
    · exact Or.inr (by simpa [bagInsert, he] using hx)

/-- Flapjack infrastructure: the HOL cardinality relation counts any support-covering sum. -/
private theorem cardRel_sum {α : Type} (b : Bag α) (n : Nat) (h : bagCardRel b n) :
    ∀ s : Finset α, (∀ x, b x ≠ 0 → x ∈ s) → ∑ x ∈ s, b x = n := by
  classical
  apply h (fun b n => ∀ s : Finset α, (∀ x, b x ≠ 0 → x ∈ s) → ∑ x ∈ s, b x = n)
  constructor
  · intro s hs
    simp [emptyBag]
  · intro b n hb e s hs
    have he : e ∈ s := hs e (by simp [bagInsert])
    have hsub : ∀ x, b x ≠ 0 → x ∈ s := by
      intro x hx
      apply hs x
      by_cases hxe : x = e
      · subst x; simp [bagInsert]
      · simpa [bagInsert, hxe] using hx
    have eq (x : α) : bagInsert e b x = b x + if x = e then 1 else 0 := by
      by_cases hx : x = e <;> simp [bagInsert, hx]
    simp only [eq, Finset.sum_add_distrib, hb s hsub]
    rw [Finset.sum_eq_single e]
    · simp
    · intro x hx hne
      simp [hne]
    · intro h
      exact (h he).elim

/-- Cardinality is monotone for a sub-bag of a finite bag. -/
@[hol "HOL/src/bag/bagScript.sml" "SUB_BAG_CARD"]
theorem subBag_card {α : Type} (a b : Bag α)
    (premises : finiteBag b ∧ subBag a b) : holBagCard a ≤ holBagCard b := by
  classical
  obtain ⟨hb, h⟩ := premises
  have ha := finiteSubBag b hb a h
  let s := (supportFinite b hb).toFinset
  have bsupport : ∀ x, b x ≠ 0 → x ∈ s := by
    intro x hx
    simpa [s] using hx
  have asupport : ∀ x, a x ≠ 0 → x ∈ s := by
    intro x hx
    apply bsupport x
    have le := h x (a x) (Nat.le_refl _)
    change a x ≤ b x at le
    omega
  have ea := cardRel_sum a (holBagCard a) (holBagCard_spec a ha) s asupport
  have eb := cardRel_sum b (holBagCard b) (holBagCard_spec b hb) s bsupport
  rw [← ea, ← eb]
  apply Finset.sum_le_sum
  intro x hx
  exact h x (a x) (Nat.le_refl _)

end Flapjack

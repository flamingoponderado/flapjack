module

public import Flapjack.Misc.Bag
import Lean.Elab.Tactic.Omega

@[expose] public section
/-! Finiteness of sub-bags. -/
namespace Flapjack

/-- Every sub-bag of a finite bag is finite. -/
@[hol "HOL/src/bag/bagScript.sml" "FINITE_SUB_BAG"]
theorem finiteSubBag {α : Type} (b : Bag α) (hb : finiteBag b) :
    ∀ a : Bag α, subBag a b → finiteBag a := by
  classical
  apply hb (fun b => ∀ a : Bag α, subBag a b → finiteBag a)
  constructor
  · intro a sub
    have azero : a = emptyBag := by
      funext x
      have h := sub x (a x) (Nat.le_refl _)
      change a x ≤ 0 at h
      simp [emptyBag]
      omega
    rw [azero]
    exact finiteEmptyBag
  · intro b ih e a sub
    have pointwise (x : α) : a x ≤ bagInsert e b x := sub x (a x) (Nat.le_refl _)
    by_cases he : a e = 0
    · refine ih a ?_
      intro x n hn
      have bound := pointwise x
      by_cases hx : x = e <;> simp [bagInn, bagInsert, hx] at bound hn ⊢ <;> omega
    · let smaller : Bag α := fun x => if x = e then a x - 1 else a x
      have smallerSub : subBag smaller b := by
        intro x n hn
        have bound := pointwise x
        by_cases hx : x = e <;> simp [bagInn, smaller, bagInsert, hx] at bound hn ⊢ <;> omega
      have eq : bagInsert e smaller = a := by
        funext x
        by_cases hx : x = e <;> simp [bagInsert, smaller, hx] <;> omega
      rw [← eq]
      exact finiteBagInsert smaller (ih smaller smallerSub) e

@[hol "HOL/src/bag/bagScript.sml" "FINITE_BAG_UNION"]
theorem finiteBagUnionIff {α : Type} (a b : Bag α) :
    finiteBag (bagUnion a b) ↔ finiteBag a ∧ finiteBag b := by
  constructor
  · intro h
    constructor
    · apply finiteSubBag _ h a
      intro x n hn
      change n ≤ a x + b x
      exact Nat.le_trans hn (Nat.le_add_right _ _)
    · apply finiteSubBag _ h b
      intro x n hn
      change n ≤ a x + b x
      exact Nat.le_trans hn (Nat.le_add_left _ _)
  · rintro ⟨ha, hb⟩
    exact finiteBagUnion a ha b hb
end Flapjack

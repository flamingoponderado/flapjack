import Flapjack.Misc.Bag
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
    · apply ih a
      intro x n hn
      change n ≤ a x at hn
      change n ≤ b x
      by_cases hx : x = e
      · subst x; omega
      · have bound := pointwise x
        simp only [bagInsert, hx, ↓reduceIte] at bound
        omega
    · let smaller : Bag α := fun x => if x = e then a x - 1 else a x
      have smallerSub : subBag smaller b := by
        intro x n hn
        change n ≤ smaller x at hn
        change n ≤ b x
        have bound := pointwise x
        by_cases hx : x = e
        · subst x
          simp [bagInsert] at bound
          simp [smaller] at hn
          omega
        · simp [bagInsert, hx] at bound
          simp [smaller, hx] at hn
          omega
      have eq : bagInsert e smaller = a := by
        funext x
        by_cases hx : x = e
        · subst x
          simp [bagInsert, smaller]
          omega
        · simp [bagInsert, smaller, hx]
      rw [← eq]
      exact finiteBagInsert smaller (ih smaller smallerSub) e

end Flapjack

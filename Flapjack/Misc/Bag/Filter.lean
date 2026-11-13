module

public import Flapjack.Misc.Bag

@[expose] public section

/-! Filtering arbitrary HOL bags by a predicate. -/
namespace Flapjack

/-- Retain the multiplicity of elements satisfying the predicate. -/
@[hol "HOL/src/bag/bagScript.sml" "BAG_FILTER_DEF"]
noncomputable def bagFilter {α : Type} (P : α → Prop) (b : Bag α) : Bag α := by
  classical
  exact fun e => if P e then b e else 0

/-- Filtering a finite bag produces a finite bag. -/
@[hol "HOL/src/bag/bagScript.sml" "FINITE_BAG_FILTER"]
theorem finiteBag_filter {α : Type} (P : α → Prop) (b : Bag α)
    (h : finiteBag b) : finiteBag (bagFilter P b) := by
  classical
  apply h (fun x => finiteBag (bagFilter P x))
  constructor
  · have eq : bagFilter P emptyBag = (emptyBag : Bag α) := by
      funext x
      simp [bagFilter, emptyBag]
    rw [eq]
    exact finiteEmptyBag
  · intro b hb e
    by_cases he : P e
    · have eq : bagFilter P (bagInsert e b) = bagInsert e (bagFilter P b) := by
        funext x
        by_cases hx : x = e <;> simp [bagFilter, bagInsert, hx, he]
      rw [eq]
      exact finiteBagInsert _ hb e
    · have eq : bagFilter P (bagInsert e b) = bagFilter P b := by
        funext x
        by_cases hx : x = e <;> simp [bagFilter, bagInsert, hx, he]
      rw [eq]
      exact hb

end Flapjack

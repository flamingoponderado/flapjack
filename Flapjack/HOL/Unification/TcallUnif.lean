module

public import Flapjack.Misc.Bag.MultisetOrder.Core

@[expose] public section

/-! Multiset ordering used by the original tail-recursive unifier. -/
namespace Flapjack.HOL.Unification

@[hol "HOL/examples/algorithms/unification/triangular/first-order/compilation/tcallUnifScript.sml" "mlt1_BAG_INSERT"]
theorem mlt1BagInsert {α : Type} (r : α → α → Prop) (b : Bag α)
    (e : α) (hb : finiteBag b) : bagMultisetStep r b (bagInsert e b) := by
  refine ⟨hb, finiteBagInsert b hb e, e, emptyBag, b, ?_, ?_, ?_⟩
  · exact (bagUnion_empty_left b).symm
  · classical
    funext x
    by_cases h : x = e <;> simp [bagInsert, bagUnion, emptyBag, h]
  · intro e' h
    simp [bagIn, bagInn, emptyBag] at h

end Flapjack.HOL.Unification

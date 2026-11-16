module

public import Flapjack.Misc.Bag
public import Mathlib.Logic.Relation

@[expose] public section

/-! The one-step multiset ordering used by HOL's unification termination proof. -/
namespace Flapjack

@[hol "HOL/src/bag/bagScript.sml" "mlt1_def"]
def bagMultisetStep {α : Type} (r : α → α → Prop) (b1 b2 : Bag α) : Prop :=
  finiteBag b1 ∧ finiteBag b2 ∧
    ∃ e rep res, b1 = bagUnion rep res ∧ b2 = bagUnion res (bagInsert e emptyBag) ∧
      ∀ e', bagIn e' rep → r e' e

private theorem stepInsert {α : Type} (r : α → α → Prop) (b : Bag α)
    (hb : finiteBag b) (e : α) : bagMultisetStep r b (bagInsert e b) := by
  refine ⟨hb, finiteBagInsert b hb e, e, emptyBag, b, ?_, ?_, ?_⟩
  · exact (bagUnion_empty_left b).symm
  · classical
    funext x
    by_cases h : x = e <;> simp [bagInsert, bagUnion, emptyBag, h]
  · intro e' h
    simp [bagIn, bagInn, emptyBag] at h

@[hol "HOL/src/bag/bagScript.sml" "TC_mlt1_FINITE_BAG"]
theorem tcMlt1FiniteBag {α : Type} (r : α → α → Prop) (b1 b2 : Bag α)
    (h : Relation.TransGen (bagMultisetStep r) b1 b2) : finiteBag b1 ∧ finiteBag b2 := by
  induction h with
  | single step => exact ⟨step.1, step.2.1⟩
  | tail _ step ih => exact ⟨ih.1, step.2.1⟩

@[hol "HOL/src/bag/bagScript.sml" "TC_mlt1_UNION2_I"]
theorem tcMlt1Union2I {α : Type} (r : α → α → Prop) (b2 b1 : Bag α)
    (h : finiteBag b2 ∧ finiteBag b1 ∧ b2 ≠ emptyBag) :
    Relation.TransGen (bagMultisetStep r) b1 (bagUnion b1 b2) := by
  have induction := h.1 (fun b => finiteBag b ∧ ∀ a, finiteBag a → b ≠ emptyBag →
      Relation.TransGen (bagMultisetStep r) a (bagUnion a b))
  have base : finiteBag (emptyBag : Bag α) ∧ ∀ a, finiteBag a →
      (emptyBag : Bag α) ≠ emptyBag →
      Relation.TransGen (bagMultisetStep r) a (bagUnion a emptyBag) := by
    exact ⟨finiteEmptyBag, fun _ _ impossible => False.elim (impossible rfl)⟩
  have next : ∀ b, (finiteBag b ∧ ∀ a, finiteBag a → b ≠ emptyBag →
      Relation.TransGen (bagMultisetStep r) a (bagUnion a b)) → ∀ e,
      finiteBag (bagInsert e b) ∧ ∀ a, finiteBag a → bagInsert e b ≠ emptyBag →
      Relation.TransGen (bagMultisetStep r) a (bagUnion a (bagInsert e b)) := by
    intro b ⟨hb, ih⟩ e
    refine ⟨finiteBagInsert b hb e, ?_⟩
    intro a ha _
    rw [(bagUnionInsert e a b).2]
    by_cases empty : b = emptyBag
    · subst b
      rw [bagUnion_empty_right]
      exact Relation.TransGen.single (stepInsert r a ha e)
    · exact (ih a ha empty).tail (stepInsert r _ (finiteBagUnion a ha b hb) e)
  exact (induction ⟨base, next⟩).2 b1 h.2.1 h.2.2

@[hol "HOL/src/bag/bagScript.sml" "TC_mlt1_UNION1_I"]
theorem tcMlt1Union1I {α : Type} (r : α → α → Prop) (b2 b1 : Bag α)
    (h : finiteBag b2 ∧ finiteBag b1 ∧ b1 ≠ emptyBag) :
    Relation.TransGen (bagMultisetStep r) b2 (bagUnion b1 b2) := by
  have comm : bagUnion b1 b2 = bagUnion b2 b1 := by
    funext x
    simp [bagUnion, Nat.add_comm]
  rw [comm]
  exact tcMlt1Union2I r b1 b2 ⟨h.2.1, h.1, h.2.2⟩

end Flapjack

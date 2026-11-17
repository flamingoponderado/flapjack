module

public import Flapjack.Misc.Bag

@[expose] public section

/-! The one-step multiset ordering used by HOL's termination proofs. -/
namespace Flapjack

@[hol "HOL/src/bag/bagScript.sml" "mlt1_def"]
def bagMultisetStep {α : Type} (r : α → α → Prop) (b1 b2 : Bag α) : Prop :=
  finiteBag b1 ∧ finiteBag b2 ∧
    ∃ e rep res, b1 = bagUnion rep res ∧ b2 = bagUnion res (bagInsert e emptyBag) ∧
      ∀ e', bagIn e' rep → r e' e

end Flapjack

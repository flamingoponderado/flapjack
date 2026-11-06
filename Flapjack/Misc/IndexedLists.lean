import Flapjack.HolRef

/-! Indexed-list operations used by the CakeML compiler proofs. -/
namespace Flapjack

/-- First occurrence of a value, or the list length when it is absent. -/
@[hol "HOL/src/list/src/indexedListsScript.sml" "findi_def"]
noncomputable def holFindi {α : Type} (value : α) (values : List α) : Nat := by
  classical
  exact match values with
    | [] => 0
    | head :: tail => if value = head then 0 else 1 + holFindi value tail

end Flapjack

import Flapjack.Misc.FindIndex

namespace Flapjack.Misc

/-- Full append equation at any starting offset. A match in the first list
wins; otherwise search resumes after its entire length. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_APPEND"]
theorem findIndexAppend {α : Type} [DecidableEq α]
    (left right : List α) (target : α) (offset : Nat) :
    findIndex target (left ++ right) offset =
      match findIndex target left offset with
      | none => findIndex target right (offset + left.length)
      | some index => some index := by
  induction left generalizing offset with
  | nil => simp [findIndex]
  | cons head tail ih =>
      by_cases equal : head = target
      · simp [findIndex, equal]
      · simpa [findIndex, equal, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (offset + 1)

end Flapjack.Misc

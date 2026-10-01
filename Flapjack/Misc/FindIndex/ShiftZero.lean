import Flapjack.Misc.FindIndex

namespace Flapjack.Misc

/-- The literal arbitrary-offset law for first-match search. The optional
result is preserved, including absence and repeated occurrences. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_shift_0"]
theorem findIndexShiftZero {α : Type} [DecidableEq α]
    (values : List α) (target : α) (offset : Nat) :
    findIndex target values offset =
      (findIndex target values 0).map (fun index => index + offset) := by
  induction values generalizing offset with
  | nil => simp [findIndex]
  | cons head tail ih =>
      by_cases equal : head = target
      · simp [findIndex, equal]
      · simp only [findIndex, if_neg equal]
        rw [ih (offset + 1), ih 1]
        cases found : findIndex target tail 0 <;>
          simp [Option.map, Nat.add_comm, Nat.add_left_comm]

end Flapjack.Misc

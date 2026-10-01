import Flapjack.Misc.FindIndex

namespace Flapjack.Misc

/-- Both literal bounds for a successful first-match search, at an arbitrary
starting offset. No zero-offset or unique-match restriction is imposed. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_LESS_LENGTH"]
theorem findIndexLessLength {α : Type} [DecidableEq α]
    (values : List α) (target : α) (offset index : Nat) :
    findIndex target values offset = some index →
      offset ≤ index ∧ index < offset + values.length := by
  induction values generalizing offset with
  | nil => simp [findIndex]
  | cons head tail ih =>
      by_cases equal : head = target
      · simp only [findIndex, if_pos equal, Option.some.injEq]
        intro found
        simp only [List.length_cons]
        omega
      · simp only [findIndex, if_neg equal]
        intro found
        have bounds := ih (offset + 1) found
        simp only [List.length_cons]
        omega

end Flapjack.Misc

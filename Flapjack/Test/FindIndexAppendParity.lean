import Flapjack.Misc.FindIndex.Append

namespace Flapjack.Misc

private def appendObservation {α : Type} [DecidableEq α]
    (left right : List α) (target : α) (offset : Nat) : Option Nat × Option Nat :=
  (findIndex target (left ++ right) offset,
    match findIndex target left offset with
    | none => findIndex target right (offset + left.length)
    | some index => some index)

example : appendObservation ([] : List Nat) [] 2 7 = (none, none) := rfl
example : appendObservation [] [1, 2] 2 7 = (some 8, some 8) := rfl
example : appendObservation [1, 2] [] 2 7 = (some 8, some 8) := rfl
example : appendObservation [2, 1] [2] 2 7 = (some 7, some 7) := rfl
example : appendObservation [1, 2, 2] [2] 2 7 = (some 8, some 8) := rfl
example : appendObservation [1, 3] [4, 2] 2 7 = (some 10, some 10) := rfl
example : appendObservation [1, 3] [4, 5] 2 7 = (none, none) := rfl
example : appendObservation [1, 3] [2] 2 0 = (some 2, some 2) := rfl
example : appendObservation [false] [false, true] true 9 = (some 11, some 11) := rfl
example : appendObservation [1] [3, 2] 2 100000000000000000000 =
    (some 100000000000000000002, some 100000000000000000002) := rfl

example {α : Type} [DecidableEq α] (left right : List α) (x : α) (n : Nat) :
    findIndex x (left ++ right) n =
      match findIndex x left n with
      | none => findIndex x right (n + left.length)
      | some index => some index := findIndexAppend left right x n

end Flapjack.Misc

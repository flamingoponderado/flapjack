import Flapjack.Misc.FindIndex.Bounds

namespace Flapjack.Test.FindIndexBoundsParity
open Flapjack.Misc
private def observation (target : Nat) (values : List Nat) (offset index : Nat) : Option Nat × Bool × Bool :=
  (findIndex target values offset, decide (offset ≤ index), decide (index < offset + values.length))
example : observation 4 [4,9] 7 7 = (some 7,true,true) := rfl
example : 7 ≤ 7 ∧ 7 < 7 + [4,9].length :=
  findIndexLessLength [4,9] 4 7 7 rfl
example : observation 9 [4,9] 7 8 = (some 8,true,true) := rfl
example : 7 ≤ 8 ∧ 8 < 7 + [4,9].length :=
  findIndexLessLength [4,9] 9 7 8 rfl
example : observation 4 [4,4] 4 4 = (some 4,true,true) := rfl
example : 4 ≤ 4 ∧ 4 < 4 + [4,4].length :=
  findIndexLessLength [4,4] 4 4 4 rfl
example : observation 9 [4,9] 4294967296 4294967297 = (some 4294967297,true,true) := rfl
example : 4294967296 ≤ 4294967297 ∧ 4294967297 < 4294967296 + [4,9].length :=
  findIndexLessLength [4,9] 9 4294967296 4294967297 rfl
example : observation 7 [1,2,3,7] 9 12 = (some 12,true,true) := rfl
example : 9 ≤ 12 ∧ 12 < 9 + [1,2,3,7].length :=
  findIndexLessLength [1,2,3,7] 7 9 12 rfl
example : observation 0 [0] 0 0 = (some 0,true,true) := rfl
example : 0 ≤ 0 ∧ 0 < 0 + [0].length :=
  findIndexLessLength [0] 0 0 0 rfl
example : observation 8 [1,2] 5 7 = (none,true,false) := rfl
example : observation 4 [] 10 10 = (none,true,false) := rfl

end Flapjack.Test.FindIndexBoundsParity

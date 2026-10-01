import Flapjack.Misc.FindIndex

namespace Flapjack.Test.FindIndexParity
open Flapjack.Misc

/-! Direct original first-match/offset observations; no substitute findi. -/
example : findIndex 2 ([] : List Nat) 0 = none := rfl
example : findIndex 2 ([2, 3] : List Nat) 7 = some 7 := rfl
example : findIndex 2 ([1, 2, 3] : List Nat) 7 = some 8 := rfl
example : findIndex 2 ([1, 3] : List Nat) 7 = none := rfl
example : findIndex 2 ([1, 2, 2] : List Nat) 3 = some 4 := rfl
example : findIndex 0 ([0, 0] : List Nat) 0 = some 0 := rfl
example : findIndex 2 ([1, 2] : List Nat) 4294967296 = some 4294967297 := rfl
example : findIndex 4 ([1, 2, 3, 4] : List Nat) 9 = some 12 := rfl

end Flapjack.Test.FindIndexParity

import Flapjack.Misc.FindIndex.ShiftZero
namespace Flapjack.Test.FindIndexShiftZeroParity
open Flapjack.Misc
-- fiz_empty=T
example : findIndex (7 : Nat) [] 4 = (findIndex (7 : Nat) [] 0).map (fun i => i + 4) := findIndexShiftZero [] 7 4
-- fiz_head=T
example : findIndex (7 : Nat) [7,2,7] 9 = (findIndex (7 : Nat) [7,2,7] 0).map (fun i => i + 9) := findIndexShiftZero [7,2,7] 7 9
-- fiz_middle=T
example : findIndex (7 : Nat) [2,7,7] 9 = (findIndex (7 : Nat) [2,7,7] 0).map (fun i => i + 9) := findIndexShiftZero [2,7,7] 7 9
-- fiz_last=T
example : findIndex (7 : Nat) [2,3,7] 9 = (findIndex (7 : Nat) [2,3,7] 0).map (fun i => i + 9) := findIndexShiftZero [2,3,7] 7 9
-- fiz_absent=T
example : findIndex (8 : Nat) [2,3,7] 9 = (findIndex (8 : Nat) [2,3,7] 0).map (fun i => i + 9) := findIndexShiftZero [2,3,7] 8 9
-- fiz_zero=T
example : findIndex (7 : Nat) [2,7,7] 0 = (findIndex (7 : Nat) [2,7,7] 0).map (fun i => i + 0) := findIndexShiftZero [2,7,7] 7 0
-- fiz_large_offset=T
example : findIndex (7 : Nat) [2,7,7] 18446744073709551616 = (findIndex (7 : Nat) [2,7,7] 0).map (fun i => i + 18446744073709551616) := findIndexShiftZero [2,7,7] 7 18446744073709551616
-- fiz_large_value=T
example : findIndex (18446744073709551617 : Nat) [2,18446744073709551617,7] 4 = (findIndex (18446744073709551617 : Nat) [2,18446744073709551617,7] 0).map (fun i => i + 4) := findIndexShiftZero [2,18446744073709551617,7] 18446744073709551617 4
-- fiz_bool=T
example : findIndex (true : Bool) [false,true,true] 9 = (findIndex (true : Bool) [false,true,true] 0).map (fun i => i + 9) := findIndexShiftZero [false,true,true] true 9
-- fiz_bool_absent=T
example : findIndex (true : Bool) [false,false] 9 = (findIndex (true : Bool) [false,false] 0).map (fun i => i + 9) := findIndexShiftZero [false,false] true 9
-- first duplicate remains the first match, even above the machine-word bound.
example : findIndex (7:Nat) [2,7,7] 18446744073709551616 = some 18446744073709551617 := by decide
end Flapjack.Test.FindIndexShiftZeroParity

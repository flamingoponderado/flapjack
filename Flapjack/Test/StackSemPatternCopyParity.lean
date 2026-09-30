import Flapjack.Compiler.Backend.Semantics.StackSem.StoreConsts

/-! Kernel replay of all twelve direct original HOL pattern-copy observations. -/
namespace Flapjack.Test.StackSemPatternCopyParity
open StackSemStoreConsts
private def observe {width : Nat} [NeZero width] (address : BitVec width) :
    Option (Nat × BitVec width × (BitVec width → WordLocW width)) →
    Option (Nat × BitVec width × WordLocW width × WordLocW width × WordLocW width)
  | none => none
  | some (j, b, m) => some (j, b, m address, m (address + BitVec.ofNat width (width / 8)), m 42)
-- zero
example : observe 10 (copyWordsForPattern (0 : BitVec 8) 0 10 3
    [7, 8] (fun _ => True) (fun _ => .loc 9 9)) =
    none := by cbv
-- one_bypass
example : observe 10 (copyWordsForPattern (1 : BitVec 8) 9 10 3
    [] (fun _ => False) (fun _ => .loc 9 9)) =
    some (9, 10, (.loc 9 9), (.loc 9 9), (.loc 9 9)) := by cbv
-- even
example : observe 10 (copyWordsForPattern (2 : BitVec 8) 0 10 3
    [7] (fun _ => True) (fun _ => .loc 9 9)) =
    some (1, 11, (.word 7), (.loc 9 9), (.loc 9 9)) := by cbv
-- odd
example : observe 10 (copyWordsForPattern (3 : BitVec 8) 0 10 3
    [7] (fun _ => True) (fun _ => .loc 9 9)) =
    some (1, 11, (.word 10), (.loc 9 9), (.loc 9 9)) := by cbv
-- multi
example : observe 10 (copyWordsForPattern (6 : BitVec 8) 0 10 3
    [7, 8] (fun _ => True) (fun _ => .loc 9 9)) =
    some (2, 12, (.word 7), (.word 11), (.loc 9 9)) := by cbv
-- missing_bitmap
example : observe 10 (copyWordsForPattern (2 : BitVec 8) 0 10 3
    [] (fun _ => True) (fun _ => .loc 9 9)) =
    none := by cbv
-- missing_domain
example : observe 10 (copyWordsForPattern (2 : BitVec 8) 0 10 3
    [7] (fun _ => False) (fun _ => .loc 9 9)) =
    none := by cbv
-- later_domain
example : observe 10 (copyWordsForPattern (4 : BitVec 8) 0 10 3
    [7, 8] (fun key => key = 10) (fun _ => .loc 9 9)) =
    none := by cbv
-- address_wrap
example : observe 255 (copyWordsForPattern (6 : BitVec 8) 0 255 3
    [7, 8] (fun _ => True) (fun _ => .loc 9 9)) =
    some (2, 1, (.word 7), (.word 11), (.loc 9 9)) := by cbv
-- value_wrap
example : observe 10 (copyWordsForPattern (3 : BitVec 8) 0 10 250
    [7] (fun _ => True) (fun _ => .loc 9 9)) =
    some (1, 11, (.word 1), (.loc 9 9), (.loc 9 9)) := by cbv
-- stride16
example : observe 10 (copyWordsForPattern (6 : BitVec 16) 0 10 3
    [7, 8] (fun _ => True) (fun _ => .loc 9 9)) =
    some (2, 14, (.word 7), (.word 11), (.loc 9 9)) := by cbv
-- stride4
example : observe 10 (copyWordsForPattern (6 : BitVec 4) 0 10 3
    [7, 8] (fun _ => True) (fun _ => .loc 9 9)) =
    some (2, 10, (.word 11), (.word 11), (.word 11)) := by cbv
end Flapjack.Test.StackSemPatternCopyParity

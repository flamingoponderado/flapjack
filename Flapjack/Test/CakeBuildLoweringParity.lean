import Flapjack.Compiler.Backend.DataToWord.Control

/-! Original HOL constant-building and allocation lowering observations. -/
namespace Flapjack.Test.CakeBuildLoweringParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Basis.Pure.MlString

private def conf : Config := ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩

#guard match Build.partsWords (width := 64) conf
    [.str (ofString "abc"), .con 0 [], .con 1 [0, 1], .int (-5)] with
  | some ((false, .word result), words) => result == 0xFFFFFFFFFFFFFFEC &&
      words == [(false, .word 0x1600000000007), (false, .word 0x636261),
                (false, .word 0x2000000000013), (true, .word 1), (false, .word 2)]
  | _ => false

#guard match Build.partsWords (width := 32) { conf with be := true }
    [.str (ofString "abcd"), .w64 0x1122334455667788, .int 2147483648] with
  | some ((true, .word result), words) => result == 1537 && words ==
      [(false, .word 0x20007), (false, .word 0x61626364), (false, .word 0), (false, .word 0x2000F),
       (false, .word 0x11223344), (false, .word 0x55667788), (false, .word 0x1000F), (false, .word 0x80000000)]
  | _ => false

-- Partial words must retain the source byte order at both target widths.
#guard match Build.partsWords (width := 32) conf [.str (ofString "abc")] with
  | some (_, [(_, _), (false, .word bytes)]) => bytes == 0x00636261
  | _ => false

#guard match Build.partsWords (width := 64) { conf with be := true } [.str (ofString "abc")] with
  | some (_, [(_, _), (false, .word bytes)]) => bytes == 0x6162630000000000
  | _ => false

-- The low half of a Word64 is zero-extended even when the target word is
-- wider than 32 bits but narrower than 64 bits.
#guard match Build.partWords (width := 48) conf .ln (.w64 0x1122334455667788) 0 with
  | some (_, [(_, _), (false, .word hi), (false, .word lo)]) =>
      hi == 0x11223344 && lo == 0x55667788
  | _ => false

-- A constructor may refer to a location already in the sparse memory.
#guard match Build.partWords (width := 64) conf
    (sptInsert 0 (true, .loc 42 7) .ln) (.con 1 [0]) 0 with
  | some (_, [(_, _), (true, .loc 42 7)]) => true
  | _ => false

#guard match storeAnyConsts (width := 64) 4 1 3 [(false, .loc 42 7)] (true, .loc 9 8) with
  | .seq (.locValue 4 42) (.seq (.store (.var 1) 4)
      (.seq (.assign 1 (.op .add [.var 1, .const 8]))
        (.seq (.set .nextFree (.var 1)) (.locValue 4 9)))) => true
  | _ => false

#guard Build.getWords (width := 32)
    [((7 : Nat), .word 3), (8, .loc 2 3), (9, .word 5)] [(10, 4)] ==
  ([(10, 4), (7, 3)], [(8, .loc 2 3), (9, .word 5)])

#guard Build.partsToWords (width := 64) conf (sptInsert 3 (true, .loc 19 2) .ln) 4 [] 16 ==
  some ((true, .loc 19 2), [])

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp (.build [.int 1, .con 0 [0]])) [] none) with
  | some (.seq (.assign 1 (.lookup .nextFree))
      (.seq (.assign 3 (.shift .lsl (.op .sub [.var 1, .lookup .currHeap]) (.const 5)))
        (.seq (.storeConsts 1 3 1 3 [(false, h), (false, v)])
          (.seq (.set .nextFree (.var 1)) (.assign 8 (.op .add [.const p, .var 3]))))), 2) =>
      h == 0x1000000000003 && v == 4 && p == 3
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp (.fromList 2)) [1, 2] none) with
  | some (.mustTerminate (.seq (.assign 1 (.const 32))
      (.call (some ([8], (.ls (), .ln), .skip, 5, 2)) (some 7) [4, 6, 1] none)), 3) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.memOp (.refByte true)) [1, 2] none) with
  | some (.seq (.assign 1 (.const 0))
      (.mustTerminate (.call (some ([8], (.ls (), .ln), .skip, 5, 2)) (some 9) [4, 6, 1] none)), 3) => true
  | _ => false

end Flapjack.Test.CakeBuildLoweringParity

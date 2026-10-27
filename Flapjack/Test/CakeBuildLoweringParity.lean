import Flapjack.Compiler.Backend.DataToWord.Control

/-! Original HOL constant-building and allocation lowering observations. -/
namespace Flapjack.Test.CakeBuildLoweringParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Basis.Pure.MlString

private def conf : Config := ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩

#guard match Build.partsWords (width := 64) conf
    [.str (ofString "abc"), .con 0 [], .con 1 [0, 1], .int (-5)] with
  | some ((false, result), words) => result == 0xFFFFFFFFFFFFFFEC &&
      words == [(false, 0x1600000000007), (false, 0x636261),
                (false, 0x2000000000013), (true, 1), (false, 2)]
  | _ => false

#guard match Build.partsWords (width := 32) { conf with be := true }
    [.str (ofString "abcd"), .w64 0x1122334455667788, .int 2147483648] with
  | some ((true, result), words) => result == 1537 && words ==
      [(false, 0x20007), (false, 0x61626364), (false, 0), (false, 0x2000F),
       (false, 0x11223344), (false, 0x55667788), (false, 0x1000F), (false, 0x80000000)]
  | _ => false

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

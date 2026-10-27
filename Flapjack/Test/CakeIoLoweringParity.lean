import Flapjack.Compiler.Backend.DataToWord.Control

/-! Pinned HOL lowering cases for integer comparison, modulo, byte bounds,
and FFI calls. -/
namespace Flapjack.Test.CakeIoLoweringParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Basis.Pure.MlString

private def conf : Config := ⟨1, 2, 3, 16, true, false, false, false, false, false, .simple⟩

#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.intOp .lessEq) [1, 2] none) with
  | some (.seq (.assign 1 (.var 4)) (.seq (.assign 3 (.var 6))
      (.seq (.assign 5 (.op .or [.var 1, .var 3]))
      (.seq (.ite .test 5 (.imm 1) .skip
        (.seq (.mustTerminate (.call (some ([1], (.ls (), .ln), .skip, 5, 2)) (some 19) [1, 3] none))
          (.assign 3 (.const 1))))
        (.ite .notLess 3 (.reg 1) (.assign 8 (.const 18)) (.assign 8 (.const 2)))))), 3) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.intOp .mod) [1, 2] none) with
  | some (.seq (.assign 1 (.op .or [.var 4, .var 6]))
      (.seq (.assign 1 (.op .or [.var 1, .shift .lsr (.var 1) (.const 63)]))
      (.ite .test 1 (.imm 1)
        (.seq (.inst (.arith (.div 1 4 6)))
          (.seq (.inst (.arith (.longMul 3 1 1 6))) (.assign 8 (.op .sub [.var 4, .var 1]))))
        (.seq (.mustTerminate (.call (some ([1], (.ls (), .ln), .skip, 5, 2)) (some 17) [4, 6] none))
          (.move 2 [(8, 1)])))), 4) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.memOp (.boundsCheckByte true)) [1, 2] none) with
  | some (.seq (.assign 1 (.op .sub [.shift .lsr
      (.load (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)])) (.const 45), .const 8]))
      (.seq (.assign 3 (.shift .ror (.var 6) (.const 2)))
        (.ite .notLower 1 (.reg 3) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.ffi (ofString "write")) [1, 2] none) with
  | some (.seq (.assign 1 (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)], .const 8]))
      (.seq (.assign 3 (.op .sub [.shift .lsr (.load (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)])) (.const 45), .const 8]))
      (.seq (.assign 5 (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 6) (.const 5)], .const 8]))
      (.seq (.assign 7 (.op .sub [.shift .lsr (.load (.op .add [.lookup .currHeap, .shift .lsr (.var 6) (.const 5)])) (.const 45), .const 8]))
      (.seq (.ffi name 1 3 5 7 (.ls (), .ln)) (.assign 8 (.const 2)))))), 2) => name == ofString "write"
  | _ => false

end Flapjack.Test.CakeIoLoweringParity

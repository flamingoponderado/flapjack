import Flapjack.Compiler.Backend.DataToWord.Control

/-! These cases mirror `data_to_word_fragment_comp_probe.out`; they check
representative source-shaped outputs and do not prove HOL correspondence. -/
namespace Flapjack.Test.DataToWordCompilerParity
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord

private def conf : Config := ⟨1, 2, 3, 16, false, false, false, false, false, false, .simple⟩

example : compileControl? (width := 64) conf 5 2 (.seq (.assign 3 (.intOp (.const (-7))) [] none) (.return [3])) =
    some (.seq (.assign 8 (.const 0xFFFFFFFFFFFFFFE4)) (.return 0 [8]), 2) := by rfl

example : compileControl? (width := 64) conf 5 9 (.assign 3 (.intOp (.const 0)) [] none) =
    some (.assign 8 (.const 0), 9) := by rfl

example : compileControl? (width := 64) conf 5 9 (.assign 3 (.intOp (.const 7)) [] none) =
    some (.assign 8 (.const 28), 9) := by rfl

example : compileControl? (width := 64) conf 5 9 (.assign 3 (.intOp (.const 4611686018427387904)) [] none) =
    some (.assign 8 (.const 0), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.globOp (.global 2)) [] none) =
    some (.assign 8 (.load (.op .add [.lookup .globReal, .const 24])), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.globOp (.setGlobal 2)) [6] none) =
    some (.seq (.store (.op .add [.lookup .globReal, .const 24]) 14) (.assign 8 (.const 2)), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.globOp (.setGlobal 2)) [6, 7] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.globOp .setGlobalsPtr) [6] none) =
    some (.seq (.set .globals (.var 14))
      (.seq (.set .globReal (.op .add [.lookup .currHeap, .shift .lsr (.var 14) (.const 5)]))
        (.assign 8 (.const 2))), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.globOp .setGlobalsPtr) [] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 32) conf 4 9 (.assign 3 (.memOp .el) [1, 2] none) =
    some (.assign 8 (.load (.op .add [
      .op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 6)],
      .op .add [.const 4, .var 6]])), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.memOp .el) [1] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.blockOp (.elemAt 2)) [1] none) =
    some (.assign 8 (.load (.op .add [
      .op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)], .const 24])), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.blockOp (.elemAt 2)) [] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.memOp .derefByte) [1] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 32) conf 4 9 (.assign 3 (.memOp .update) [1, 2, 3] none) =
    some (.seq (.store (.op .add [
      .op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 6)],
      .op .add [.const 4, .var 6]]) 8) (.assign 8 (.const 2)), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.memOp .updateCons) [1, 2, 3] none) =
    some (.seq (.store (.op .add [
      .op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)],
      .op .add [.const 8, .shift .lsl (.var 6) (.const 1)]]) 8) (.assign 8 (.const 2)), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.memOp .update) [1, 2] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.memOp .updateByte) [1, 2, 3] none) =
    some (.seq (.assign 1 (.op .add [
      .op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)],
      .op .add [.const 8, .shift .lsr (.var 6) (.const 2)]]))
      (.seq (.assign 3 (.shift .lsr (.var 8) (.const 2)))
        (.seq (.inst (.mem .store8 3 (.addr 1 0))) (.assign 8 (.const 2)))), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.memOp .updateByte) [] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9
    (.assign 3 (.thunkOp (.updateThunk .notEvaluated)) [1, 2] none) =
    some (.seq (.store (.op .add [
      .op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)], .const 8]) 6)
      (.assign 8 (.const 2)), 9) := by rfl

example : compileControl? (width := 64) conf 4 9
    (.assign 3 (.thunkOp (.updateThunk .evaluated)) [1, 2] none) =
    some (.seq (.assign 1 (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)]))
      (.seq (.assign 3 (.const 0x100000000003B)) (.seq (.store (.var 1) 3)
        (.seq (.store (.op .add [.var 1, .const 8]) 6) (.assign 8 (.const 2))))), 9) := by rfl

example : compileControl? (width := 64) { conf with lenSize := 0 } 4 9
    (.assign 3 (.thunkOp (.updateThunk .evaluated)) [1, 2] none) =
    some (.seq (.assign 1 (.const (-1))) (.alloc 1 (adjustSets (.ln : NumSet))), 9) := by rfl

example : compileControl? (width := 64) conf 4 9
    (.assign 3 (.thunkOp (.updateThunk .evaluated)) [1] none) = some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.blockOp .boolNot) [] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.memOp .finaliseCons) [1] none) =
    some (.assign 8 (.var 4), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.memOp .finaliseCons) [1, 2] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 32) conf 4 9 (.assign 3 (.memOp .lengthByte) [1] none) =
    some (.assign 8 (.shift .lsl (.op .sub [
      .shift .lsr (.load (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 6)])) (.const 14),
      .const 4]) (.const 2)), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.memOp .lengthByte) [] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.blockOp .lengthBlock) [1] none) =
    some (.ite .test 4 (.imm 1) (.assign 8 (.const 0))
      (.assign 8 (.shift .lsl (.shift .lsr (.load
        (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)])) (.const 48)) (.const 2))), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.blockOp .lengthBlock) [] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.intOp (.lessConstSmall 25)) [1, 2] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.blockOp (.boolTest (.compare .lt))) [1, 2] none) =
    some (.ite .equal 4 (.reg 6) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 9) := by rfl

example : compileControl? (width := 64) conf 4 9 (.assign 3 (.blockOp (.boolTest .equal)) [1] none) =
    some (.skip, 9) := by rfl

example : compileControl? (width := 64) conf 5 2 (.ifThenElse 1 (.move 3 1) (.seq .tick (.return [1, 3]))) =
    some (.ite .equal 4 (.imm 18) (.move 0 [(8, 4)]) (.seq .tick (.return 0 [4, 8])), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp .boolNot) [1] none) =
    some (.assign 8 (.op .xor [.var 4, .const 16]), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.boolTest .equal)) [1, 2] none) =
    some (.ite .equal 4 (.reg 6) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.intOp (.lessConstSmall 25)) [1] none) =
    some (.ite .less 4 (.imm 100) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.lenEq 0)) [1] none) =
    some (.ite .test 4 (.imm 1) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.tagLenEq 17 0)) [1] none) =
    some (.ite .equal 4 (.imm 274) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.tagLenEq 1152921504606846976 0)) [1] none) =
    some (.assign 8 (.const 2), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.tagLenEq 0 1)) [1] none) =
    some (.seq (.assign 1 (.op .and [.var 4, .const 15]))
      (.ite .equal 1 (.imm 3) (.assign 8 (.const 18)) (.assign 8 (.const 2))), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.tagLenEq 1 3)) [1] none) =
    some (.seq (.assign 1 (.const 0))
      (.seq (.ite .test 4 (.imm 1) .skip (.assign 1 (.load (realAddr conf 4))))
        (.ite .equal 1 (.imm 0x3000000000013) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.tagLenEq 1 65536)) [1] none) =
    some (.assign 8 (.const 2), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp .boundsCheckBlock) [1, 2] none) =
    some (.seq (.ite .test 4 (.imm 1) (.assign 1 (.const 0))
      (.assign 1 (shiftN .lsr (.load (realAddr conf 4)) 48)))
      (.seq (.assign 3 (shiftN .ror (.var 6) 2))
        (.ite .lower 3 (.reg 1) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp (.boundsCheckByte false)) [1, 2] none) =
    some (.seq (.assign 1 (.op .sub [shiftN .lsr (.load (realAddr conf 4)) 45, .const 8]))
      (.seq (.assign 3 (shiftN .ror (.var 6) 2))
        (.ite .lower 3 (.reg 1) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp (.boundsCheckByte true)) [1, 2] none) =
    some (.seq (.assign 1 (.op .sub [shiftN .lsr (.load (realAddr conf 4)) 45, .const 8]))
      (.seq (.assign 3 (shiftN .ror (.var 6) 2))
        (.ite .notLower 1 (.reg 3) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .boundsCheckArray) [1, 2] none) =
    some (.seq (.assign 1 (shiftN .lsr (.load (realAddr conf 4)) 48))
      (.seq (.assign 3 (shiftN .ror (.var 6) 2))
        (.ite .lower 3 (.reg 1) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .length) [1] none) =
    some (.assign 8 (shiftN .lsl (shiftN .lsr (.load (realAddr conf 4)) 48) 2), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .lengthByte) [1] none) =
    some (.assign 8 (shiftN .lsl (.op .sub [shiftN .lsr (.load (realAddr conf 4)) 45, .const 8]) 2), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .el) [1, 2] none) =
    some (.assign 8 (.load (.op .add [realAddr conf 4,
      .op .add [.const 8, .shift .lsl (.var 6) (.const 1)]])), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .derefByte) [1, 2] none) =
    some (.seq (.assign 1 (.op .add [realAddr conf 4, .op .add [.const 8, shiftN .lsr (.var 6) 2]]))
      (.seq (.inst (.mem .load8 3 (.addr 1 0))) (.assign 8 (shiftN .lsl (.var 3) 2))), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.cons 17)) [] none) =
    some (.assign 8 (.const 274), 2) := by rfl

example : compileControl? (width := 64) conf 5 2 (.assign 3 (.label 42) [] none) = some (.locValue 8 42, 2) := by rfl
example : compileControl? (width := 64) conf 5 2 (.assign 3 (.globOp .globalsPtr) [] none) =
    some (.assign 8 (.lookup .globals), 2) := by rfl

end Flapjack.Test.DataToWordCompilerParity

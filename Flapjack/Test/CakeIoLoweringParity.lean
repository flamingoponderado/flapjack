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


#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.wordOp (.wordOpw .w64 .add)) [1, 2] none) with
  | some (.seq (.assign 3 (.op .add [
      .load (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)], .const 8]),
      .load (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 6) (.const 5)], .const 8])]))
    (.seq (.assign 1 (.lookup .nextFree)) (.seq (.store (.op .add [.var 1, .const 8]) 3)
    (.seq (.assign 3 (.const h)) (.seq (.store (.var 1) 3)
    (.seq (.set .nextFree (.op .add [.var 1, .const 16]))
      (.assign 8 (.op .or [.shift .lsl (.op .sub [.var 1, .lookup .currHeap]) (.const 5), .const 1]))))))), 2) =>
      h == 0x100000000000F
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.memOp .boundsCheckArray) [1, 2] none) with
  | some (.seq (.assign 1 (.shift .lsr (.load (.op .add [.lookup .currHeap,
        .shift .lsr (.var 4) (.const 5)])) (.const 48)))
      (.seq (.assign 3 (.shift .ror (.var 6) (.const 2)))
        (.ite .lower 3 (.reg 1) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) => true
  | _ => false

-- The append call reverses the argument registers, as in the pinned HOL probe.
#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp .listAppend) [1, 2] none) with
  | some (.mustTerminate (.call (some ([8], (.ls (), .ln), .skip, 5, 2))
      (some 33) [6, 4] none), 3) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp .listAppend) [1] none) with
  | some (.skip, 2) => true
  | _ => false

-- Original data_to_word$comp results captured by cake_io_lowering_probe.
#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.memOp .xorByte) [1, 2] none) with
  | some (.seq (.assign 1 (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)]))
      (.seq (.assign 3 (.op .add [.lookup .currHeap, .shift .lsr (.var 6) (.const 5)]))
      (.seq (.assign 5 (.shift .lsr (.load (.var 3)) (.const 48)))
      (.seq (.assign 1 (.op .add [.var 1, .const 8]))
      (.seq (.assign 3 (.op .add [.var 3, .const 8]))
        (.mustTerminate (.call (some ([8], (.ls (), .ln), .skip, 5, 2))
          (some 36) [1, 3, 5] none)))))), 3) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.memOp .configGC) [1, 2] none) with
  | some (.seq .skip (.seq (.assign 1 (.const 0))
      (.seq (.alloc 1 (.ls (), .ln)) (.seq .skip (.assign 8 (.const 2))))), 2) => true
  | _ => false

#guard match compileControl? (width := 64) { conf with callEmptyFfi := true } 5 2
    (.assign 3 (.memOp .configGC) [1, 2] none) with
  | some (.seq (.seq (.assign 3 (.const 0))
      (.seq (.assign 7 (.op .sub [.lookup .nextFree, .lookup .currHeap]))
      (.seq (.assign 9 (.lookup .heapLength)) (.ffi n 7 3 9 3 (.ls (), .ln)))))
      (.seq (.assign 1 (.const 0)) (.seq (.alloc 1 (.ls (), .ln))
      (.seq (.seq (.assign 3 (.const 0))
      (.seq (.assign 7 (.op .sub [.lookup .nextFree, .lookup .currHeap]))
      (.seq (.assign 9 (.lookup .heapLength)) (.ffi m 7 3 9 3 (.ls (), .ln)))))
      (.assign 8 (.const 2))))), 2) => n == ofString "" && m == ofString ""
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.memOp .xorByte) [1] none) with
  | some (.skip, 2) => true
  | _ => false

-- LenEq uses an immediate for short blocks and the header for longer ones.
#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp (.lenEq 0)) [1] none) with
  | some (.ite .test 4 (.imm 1) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 2) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp (.lenEq 1)) [1] none) with
  | some (.seq (.assign 1 (.op .and [.var 4, .const 7]))
      (.ite .equal 1 (.imm 3) (.assign 8 (.const 18)) (.assign 8 (.const 2))), 2) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp (.lenEq 3)) [1] none) with
  | some (.seq (.assign 1 (.const 0))
      (.seq (.ite .test 4 (.imm 1) .skip
        (.assign 1 (.shift .lsr (.load (.op .add [.lookup .currHeap,
          .shift .lsr (.var 4) (.const 5)])) (.const 48))))
        (.ite .equal 1 (.imm 3) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp (.lenEq 18446744073709551616)) [1] none) with
  | some (.assign 8 (.const 2), 2) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp (.lenEq 1)) [] none) with
  | some (.skip, 2) => true
  | _ => false

private def matchesWord64Shift (shift : Shift) (amount expected : Nat) : Bool :=
  match compileControl? (width := 64) conf 5 2
      (.assign 3 (.wordOp (.wordShift .w64 shift amount)) [1] none) with
  | some (.seq (.assign 3 (.load (.op .add [.op .add [.lookup .currHeap,
        .shift .lsr (.var 4) (.const 5)], .const 8])))
      (.seq (.assign 3 (.shift actual (.var 3) (.const n)))
      (.seq (.assign 1 (.lookup .nextFree)) (.seq (.store (.op .add [.var 1, .const 8]) 3)
      (.seq (.assign 3 (.const h)) (.seq (.store (.var 1) 3)
      (.seq (.set .nextFree (.op .add [.var 1, .const 16]))
        (.assign 8 (.op .or [.shift .lsl (.op .sub [.var 1, .lookup .currHeap]) (.const 5), .const 1])))))))), 2) =>
      decide (actual = shift) && n.toNat == expected && h == 0x100000000000F
  | _ => false

#guard matchesWord64Shift .lsl 5 5
#guard matchesWord64Shift .ror 65 1
#guard matchesWord64Shift .asr 65 63

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.blockOp .boundsCheckBlock) [1, 2] none) with
  | some (.seq (.ite .test 4 (.imm 1) (.assign 1 (.const 0))
      (.assign 1 (.shift .lsr (.load (.op .add [.lookup .currHeap,
        .shift .lsr (.var 4) (.const 5)])) (.const 48))))
      (.seq (.assign 3 (.shift .ror (.var 6) (.const 2)))
        (.ite .lower 3 (.reg 1) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) => true
  | _ => false

private def matchesWord64Store : WordLangProgHOL (BitVec 64) → Bool
  | .seq (.assign 1 (.lookup .nextFree)) (.seq (.store (.op .add [.var 1, .const 8]) 3)
      (.seq (.assign 3 (.const h)) (.seq (.store (.var 1) 3)
      (.seq (.set .nextFree (.op .add [.var 1, .const 16]))
        (.assign 8 (.op .or [.shift .lsl (.op .sub [.var 1, .lookup .currHeap]) (.const 5), .const 1])))))) =>
      h == 0x100000000000F
  | _ => false

#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp .wordFromInt) [1] none) with
  | some (.seq (.ite .test 4 (.imm 1) (.assign 3 (.shift .asr (.var 4) (.const 2)))
      (.seq (.seq (.assign 3 (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)]))
          (.seq (.assign 1 (.load (.var 3))) (.assign 3 (.load (.op .add [.var 3, .const 8])))))
        (.ite .test 1 (.imm 16) .skip (.assign 3 (.op .sub [.const 0, .var 3]))))) stored, 2) =>
      matchesWord64Store stored
  | _ => false

#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp .wordToInt) [1] none) with
  | some (.seq (.assign 3 (.load (.op .add [.op .add [.lookup .currHeap,
        .shift .lsr (.var 4) (.const 5)], .const 8])))
      (.seq (.assign 1 (.shift .lsr (.var 3) (.const 61)))
        (.ite .equal 1 (.imm 0) (.assign 8 (.shift .lsl (.var 3) (.const 2))) stored)), 2) =>
      matchesWord64Store stored
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.memOp (.stringCmp false .lt)) [1, 2] none) with
  | some (.seq (.assign 1 (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)]))
      (.seq (.assign 3 (.op .add [.lookup .currHeap, .shift .lsr (.var 6) (.const 5)]))
      (.seq (.assign 5 (.shift .lsr (.load (.var 1)) (.const 45)))
      (.seq (.assign 7 (.shift .lsr (.load (.var 3)) (.const 45)))
      (.seq (.seq (.assign 11 (.op .add [.var 1, .const 8]))
        (.seq (.assign 13 (.op .add [.var 3, .const 8]))
        (.seq (.assign 9 (.var 5)) (.seq (.ite .lower 7 (.reg 5) (.assign 9 (.var 7)) .skip)
          (.mustTerminate (.call (some ([5, 7], (.ls (), .ln), .skip, 5, 2)) (some 38) [11, 13, 9, 5, 7] none))))))
        (.ite .lower 5 (.reg 7) (.assign 8 (.const 18)) (.assign 8 (.const 2))))))), 3) => true
  | _ => false

#guard match compileControl? (width := 64) conf 5 2
    (.assign 3 (.memOp (.stringCmp true .geq)) [1, 2] none) with
  | some (.seq (.assign 1 (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)]))
      (.seq (.assign 3 (.op .add [.lookup .currHeap, .shift .lsr (.var 6) (.const 5)]))
      (.seq (.assign 5 (.shift .lsr (.load (.var 1)) (.const 45)))
      (.seq (.assign 7 (.shift .lsr (.load (.var 3)) (.const 45)))
      (.seq (.ite .equal 5 (.reg 7) (.seq (.assign 11 (.op .add [.var 1, .const 8]))
        (.seq (.assign 13 (.op .add [.var 3, .const 8]))
          (.mustTerminate (.call (some ([5, 7], (.ls (), .ln), .skip, 5, 2)) (some 38) [11, 13, 7, 7, 7] none)))) .skip)
        (.ite .notLower 5 (.reg 7) (.assign 8 (.const 18)) (.assign 8 (.const 2))))))), 3) => true
  | _ => false

private def matchesFpFallback (op : ClosLang.WordOp) (args : List Nat) : Bool :=
  match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp op) args none) with
  | some (.seq (.assign 1 (.const value)) (.alloc 1 (.ls (), .ln)), 2) => value == 0xffffffffffffffff
  | _ => false

#guard matchesFpFallback (.fpCmp .less) [1, 2]
#guard matchesFpFallback (.fpBop .add) [1, 2]
#guard matchesFpFallback (.fpUop .neg) [1]
#guard matchesFpFallback (.fpTop .fma) [1, 2, 3]
#guard match compileControl? (width := 64) { conf with hasFpOps := true, hasFpTern := false } 5 2
    (.assign 3 (.wordOp (.fpTop .fma)) [1, 2, 3] none) with
  | some (.seq (.assign 1 (.const value)) (.alloc 1 (.ls (), .ln)), 2) => value == 0xffffffffffffffff
  | _ => false
#guard (compileControl? (width := 64) { conf with hasFpOps := true } 5 2
  (.assign 3 (.wordOp (.fpBop .add)) [1, 2] none)).isNone
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp (.fpUop .neg)) [] none) with
  | some (.skip, 2) => true
  | _ => false

end Flapjack.Test.CakeIoLoweringParity

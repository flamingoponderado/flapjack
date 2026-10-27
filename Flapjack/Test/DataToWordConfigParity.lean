import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.DataToWord.Header
import Flapjack.Compiler.Backend.DataToWord.Locations
import Flapjack.Compiler.Backend.DataToWord.WordOp
import Flapjack.Compiler.Backend.DataToWord.Control
import Flapjack.Compiler.Backend.DataToWord.Stubs
import Flapjack.Test.CakeMLFlatOracle

/-!
# `data_to_word` configuration helpers: original-oracle rows

Kernel replay of the six rows of `scripts/hol-probes/data_to_word_config_probe.out`.
-/

namespace Flapjack.Test.DataToWordConfigParity

open Flapjack.Compiler.Backend.DataToWord

private def conf : Config :=
  { tagBits := 1, lenBits := 2, padBits := 3, lenSize := 16, hasDiv := false,
    hasLongdiv := false, hasFpOps := false, hasFpTern := false, be := false,
    callEmptyFfi := false, gcKind := .simple }

-- shift_length=8
example : shiftLength conf = 8 := rfl
-- small_shift_length=4
example : smallShiftLength conf = 4 := rfl
-- gen_size_nil_64=0xFFFFFFFFFFFFFFF8w
example : (getGenSize [] : BitVec 64) = 0xFFFFFFFFFFFFFFF8 := by decide
-- gen_size_ten_64=80w
example : (getGenSize [10, 20] : BitVec 64) = 80 := by decide
-- gen_size_overflow_64=0xFFFFFFFFFFFFFFF8w
example : (getGenSize [2305843009213693952] : BitVec 64) = 0xFFFFFFFFFFFFFFF8 := by decide
-- gen_size_three_32=12w
example : (getGenSize [3] : BitVec 32) = 12 := by decide

private def headerConfig : Config := { conf with lenSize := 4 }
#guard match encodeHeader (width := 64) headerConfig 3 5 with
  | some w => w.toNat == 5764607523034234895
  | none => false
#guard (encodeHeader (width := 64) headerConfig 3 16).isNone
#guard match encodeHeader (width := 32) headerConfig 3 5 with
  | some w => w.toNat == 1342177295
  | none => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_header

#guard [fromListLocation, fromList1Location, refByteLocation, refArrayLocation, replicateLocation, anyArithLocation, addLocation, subLocation, mulLocation, divLocation, modLocation, compare1Location, compareLocation, equal1Location, equalLocation, longDiv1Location, longDivLocation, memCopyLocation, byteCopyLocation, byteCopyAddLocation, byteCopySubLocation, byteCopyNewLocation, installLocation, installCodeLocation, installDataLocation, dummyLocation, appendLocation, appendMainLoopLocation, appendLenLoopLocation, xorLoopLocation, unusedLocation, stringCmpLoopLocation, bignumLocation] == (List.range 33).map (fun n => n + 7)
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_locations
#guard decide ([lookupWordOp .andw, lookupWordOp .orw, lookupWordOp .xor, lookupWordOp .add, lookupWordOp .sub] =
  [.bitwise .and, .bitwise .or, .bitwise .xor, .carried .add, .carried .sub])
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_word_ops
#guard match compileControl? (width := 64) conf 5 2 (.return [0, 3]) with
  | some (.return 0 [2, 8], 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.call none (some 9) [0, 3] none) with
  | some (.call none (some 9) [0, 2, 8] none, 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 0 (.intOp .add) [] none) with
  | some (.skip, 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_control
#guard match compileControl? (width := 64) conf 5 2 (.makeSpace 2 .ln) with
  | some (.seq (.assign 1 (.op .sub [.lookup .triggerGC, .lookup .nextFree]))
      (.ite .lower 1 (.imm 16)
        (.seq .skip (.seq (.assign 1 (.const 16)) (.seq (.alloc 1 (.ls (), .ln)) .skip))) .skip), 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_space
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.intOp (.const (-3))) [] none) with
  | some (.assign 8 (.const w), 2) => w == (-12 : BitVec 64)
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.globOp .globalsPtr) [] none) with
  | some (.assign 8 (.lookup .globals), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.label 12) [] none) with
  | some (.locValue 8 12, 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_assign
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.globOp (.global 3)) [] none) with
  | some (.assign 8 (.load (.op .add [.lookup .globReal, .const 32])), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.globOp (.setGlobal 3)) [1] none) with
  | some (.seq (.store (.op .add [.lookup .globReal, .const 32]) 4) (.assign 8 (.const 2)), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.globOp (.setGlobal 3)) [] none) with
  | some (.skip, 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_globals
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.elemAt 2)) [1] none) with
  | some (.assign 8 (.load (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)], .const 24])), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .el) [1, 2] none) with
  | some (.assign 8 (.load (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)],
      .op .add [.const 8, .shift .lsl (.var 6) (.const 1)]])), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp .boolNot) [1] none) with
  | some (.assign 8 (.op .xor [.var 4, .const 16]), 2) => true
  | _ => false
#guard match compileControl? (width := 32) conf 5 2 (.assign 3 (.memOp .el) [1, 2] none) with
  | some (.assign 8 (.load (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 6)],
      .op .add [.const 4, .var 6]])), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.globOp .setGlobalsPtr) [1] none) with
  | some (.seq (.set .globals (.var 4)) (.seq (.set .globReal
      (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)])) (.assign 8 (.const 2))), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.globOp .setGlobalsPtr) [] none) with
  | some (.skip, 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .update) [1, 2, 3] none) with
  | some (.seq (.store (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)],
      .op .add [.const 8, .shift .lsl (.var 6) (.const 1)]]) 8) (.assign 8 (.const 2)), 2) => true
  | _ => false
#guard match compileControl? (width := 32) conf 5 2 (.assign 3 (.memOp .updateCons) [1, 2, 3] none) with
  | some (.seq (.store (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 6)],
      .op .add [.const 4, .var 6]]) 8) (.assign 8 (.const 2)), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .update) [1] none) with
  | some (.skip, 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_loads
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .ref) [1] none) with
  | some (.seq (.set .triggerGC (.op .sub [.lookup .triggerGC, .const 16]))
      (.seq (.assign 1 (.op .sub [.lookup .endOfHeap, .const 16]))
       (.seq (.set .endOfHeap (.var 1))
        (.seq (.assign 3 (.const 281474976710667))
         (.seq (.seq (.store (.op .add [.var 1, .const 0]) 3)
          (.seq (.store (.op .add [.var 1, .const 8]) 4) .skip))
          (.assign 8 (.op .or [.shift .lsl (.op .sub [.var 1, .lookup .currHeap]) (.const 5), .const 1])))))), 2) => true
  | _ => false
#guard match compileControl? (width := 64) { conf with lenSize := 0 } 5 2 (.assign 3 (.memOp .ref) [1] none) with
  | some (.seq (.assign 1 (.const w)) (.alloc 1 (.ls (), .ln)), 2) => w == (-1 : BitVec 64)
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_ref
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.intOp .add) [1, 2] none) with
  | some (.seq (.inst (.arith (.addOverflow 1 4 6 3)))
      (.seq (.assign 3 (.op .or [.var 3, .var 4, .var 6]))
       (.seq (.ite .test 3 (.imm 1) .skip
        (.mustTerminate (.call (some ([1], (.ls (), .ln), .skip, 5, 2)) (some 13) [4, 6] none)))
        (.move 2 [(8, 1)]))), 3) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.intOp .sub) [1, 2] none) with
  | some (.seq (.inst (.arith (.subOverflow 1 4 6 3)))
      (.seq (.assign 3 (.op .or [.var 3, .var 4, .var 6]))
       (.seq (.ite .test 3 (.imm 1) .skip
        (.mustTerminate (.call (some ([1], (.ls (), .ln), .skip, 5, 2)) (some 14) [4, 6] none)))
        (.move 2 [(8, 1)]))), 3) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.intOp .less) [1, 2] none) with
  | some (.seq (.assign 1 (.var 4)) (.seq (.assign 3 (.var 6))
      (.seq (.assign 5 (.op .or [.var 1, .var 3]))
       (.seq (.ite .test 5 (.imm 1) .skip
        (.seq (.mustTerminate (.call (some ([1], (.ls (), .ln), .skip, 5, 2)) (some 19) [1, 3] none)) (.assign 3 (.const 1))))
        (.ite .less 1 (.reg 3) (.assign 8 (.const 18)) (.assign 8 (.const 2)))))), 3) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_int
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp .equal) [1, 2] none) with
  | some (.seq (.assign 1 (.var 4)) (.seq (.assign 3 (.var 6))
      (.seq (.assign 5 (.op .and [.var 1, .var 3]))
       (.seq (.ite .test 5 (.imm 1) .skip (.ite .equal 1 (.reg 3) .skip
        (.seq (.mustTerminate (.call (some ([1], (.ls (), .ln), .skip, 5, 2)) (some 21) [1, 3] none))
         (.assign 3 (.const 1)))))
        (.ite .equal 1 (.reg 3) (.assign 8 (.const 18)) (.assign 8 (.const 2)))))), 3) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp .equal) [1] none) with
  | some (.skip, 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .refArray) [1, 2] none) with
  | some (.seq (.ite .test 4 (.imm 1) .skip (.seq (.assign 1 (.const fail)) (.alloc 1 (.ls (), .ln))))
      (.seq (.move 0 [(1, 4)])
       (.seq (.seq (.assign 1 (.shift .lsr (.var 1) (.const 2)))
        (.seq (.ite .lower 1 (.imm 65536)
         (.assign 1 (.shift .lsl (.op .add [.var 1, .const 1]) (.const 3))) (.assign 1 (.const tooLarge)))
         (.seq (.assign 3 (.op .sub [.lookup .triggerGC, .lookup .nextFree]))
          (.ite .lower 3 (.reg 1) (.seq .skip (.seq (.alloc 1 cut) .skip)) .skip))))
        (.mustTerminate (.call (some ([8], (.ls (), .ln), .skip, 5, 2)) (some 10) [4, 6] none)))), 3) =>
      fail == (-1 : BitVec 64) && tooLarge == (-1 : BitVec 64) &&
        decide (cut = adjustSets (Flapjack.sptListInsert [1, 2] .ln))
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .refArray) [1] none) with
  | some (.skip, 2) => true
  | _ => false
#guard match compileControl? (width := 64) { conf with callEmptyFfi := true } 5 2
    (.assign 3 (.memOp .refArray) [1, 2] none) with
  | some (.seq _ (.seq _ (.seq (.seq _ (.seq _ (.seq _ (.ite .lower 3 (.reg 1)
      (.seq (.seq (.assign 3 (.const 0)) (.seq (.assign 7 _) (.seq (.assign 9 _) (.ffi _ 7 3 9 3 before))))
        (.seq (.alloc 1 cut)
          (.seq (.assign 3 (.const 0)) (.seq (.assign 7 _) (.seq (.assign 9 _) (.ffi _ 7 3 9 3 after)))))) .skip)))) _)), 3) =>
      decide (cut = adjustSets (Flapjack.sptListInsert [1, 2] .ln)) &&
      decide (before = (cut.1, Flapjack.sptInsert 1 () cut.2)) && decide (after = cut)
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_ref_array
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .length) [1] none) with
  | some (.assign 8 (.shift .lsl (.shift .lsr (.load (.op .add [.lookup .currHeap,
      .shift .lsr (.var 4) (.const 5)])) (.const 48)) (.const 2)), 2) => true
  | _ => false
#guard match compileControl? (width := 32) conf 5 2 (.assign 3 (.memOp .lengthByte) [1] none) with
  | some (.assign 8 (.shift .lsl (.op .sub [.shift .lsr (.load (.op .add [.lookup .currHeap,
      .shift .lsr (.var 4) (.const 6)])) (.const 14), .const 4]) (.const 2)), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp .lengthBlock) [1] none) with
  | some (.ite .test 4 (.imm 1) (.assign 8 (.const 0)) (.assign 8 (.shift .lsl (.shift .lsr
      (.load (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)])) (.const 48)) (.const 2))), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.tagLenEq 0 0)) [1] none) with
  | some (.ite .equal 4 (.imm 2) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.tagLenEq 0 1)) [1] none) with
  | some (.seq (.assign 1 (.op .and [.var 4, .const 15]))
      (.ite .equal 1 (.imm 3) (.assign 8 (.const 18)) (.assign 8 (.const 2))), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.tagLenEq 1 1)) [1] none) with
  | some (.seq (.assign 1 (.const 0)) (.seq (.ite .test 4 (.imm 1) .skip
      (.assign 1 (.load (.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)]))))
      (.ite .equal 1 (.imm 281474976710675) (.assign 8 (.const 18)) (.assign 8 (.const 2)))), 2) => true
  | _ => false
#guard match compileControl? (width := 64) { conf with lenSize := 0 } 5 2
    (.assign 3 (.blockOp (.tagLenEq 1 1)) [1] none) with
  | some (.assign 8 (.const 2), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.tagLenEq 0 1)) [] none) with
  | some (.skip, 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_lengths
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .derefByte) [1, 2] none) with
  | some (.seq (.assign 1 (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)],
      .op .add [.const 8, .shift .lsr (.var 6) (.const 2)]]))
      (.seq (.inst (.mem .load8 3 (.addr 1 0))) (.assign 8 (.shift .lsl (.var 3) (.const 2)))), 2) => true
  | _ => false
#guard match compileControl? (width := 32) conf 5 2 (.assign 3 (.memOp .updateByte) [1, 2, 3] none) with
  | some (.seq (.assign 1 (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 6)],
      .op .add [.const 4, .shift .lsr (.var 6) (.const 2)]]))
      (.seq (.assign 3 (.shift .lsr (.var 8) (.const 2)))
        (.seq (.inst (.mem .store8 3 (.addr 1 0))) (.assign 8 (.const 2)))), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp .derefByte) [1] none) with
  | some (.skip, 2) => true
  | _ => false
#guard match compileControl? (width := 32) conf 5 2 (.assign 3 (.memOp .updateByte) [1, 2] none) with
  | some (.skip, 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_byte_memory
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.equalConst (.int (-3)))) [1] none) with
  | some (.ite .equal 4 (.imm n) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 2) => n == (-12 : BitVec 64)
  | _ => false
#guard (compileControl? (width := 8) conf 5 2 (.assign 3 (.blockOp (.equalConst (.int 32))) [1] none)).isNone
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp (.copyByte true)) [1, 2, 3] none) with
  | some (.mustTerminate (.call (some ([8], (.ls (), .ln), .skip, 5, 2)) (some 28) [4, 6, 8] none), 3) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp (.copyByte false)) [1, 2, 3, 4, 5] none) with
  | some (.mustTerminate (.call (some ([8], (.ls (), .ln), .skip, 5, 2)) (some 25) [4, 6, 8, 10, 12] none), 3) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.memOp (.copyByte false)) [1, 2] none) with
  | some (.skip, 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.thunkOp (.updateThunk .notEvaluated)) [1, 2] none) with
  | some (.seq (.store (.op .add [.op .add [.lookup .currHeap, .shift .lsr (.var 4) (.const 5)], .const 8]) 6)
      (.assign 8 (.const 2)), 2) => true
  | _ => false
#guard match compileControl? (width := 64) { conf with lenSize := 0 } 5 2
    (.assign 3 (.thunkOp (.updateThunk .evaluated)) [1, 2] none) with
  | some (.seq (.assign 1 (.const w)) (.alloc 1 (.ls (), .ln)), 2) => w == (-1 : BitVec 64)
  | _ => false
#guard match compileControl? (width := 8) conf 5 2 (.assign 3 (.blockOp (.cons 1)) [1] none) with
  | some (.seq (.assign 1 (.const w)) (.alloc 1 (.ls (), .ln)), 2) => w == (-1 : BitVec 8)
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_runtime_ops
#guard match compileStub? (width := 64) memCopyLocation with
  | some (5, .ite .test 2 (.reg 2) (.return 0 [8])
      (.seq (.assign 1 (.load (.var 4))) (.seq (.assign 2 (.op .sub [.var 2, .const 4]))
       (.seq (.assign 4 (.op .add [.var 4, .const 8])) (.seq (.store (.var 6) 1)
        (.seq (.assign 6 (.op .add [.var 6, .const 8])) (.call none (some 24) [0, 2, 4, 6, 8] none))))))) => true
  | _ => false
#guard match compileStub? (width := 32) stringCmpLoopLocation with
  | some (6, .ite .equal 6 (.imm 4) (.return 0 [8, 10])
      (.seq (.inst (.mem .load8 1 (.addr 2 0))) (.seq (.inst (.mem .load8 3 (.addr 4 0)))
       (.seq (.ite .notEqual 1 (.reg 3) (.return 0 [1, 3]) .skip)
        (.seq (.assign 2 (.op .add [.var 2, .const 1])) (.seq (.assign 4 (.op .add [.var 4, .const 1]))
         (.seq (.assign 6 (.op .sub [.var 6, .const 1])) (.call none (some 38) [0, 2, 4, 6, 8, 10] none)))))))) => true
  | _ => false
#guard match compileStub? (width := 64) byteCopyNewLocation with
  | some (4, .skip) => true
  | _ => false
#guard (compileStub? (width := 64) refArrayLocation).isNone
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_stubs
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.blockOp (.boolTest (.compare .gt))) [1, 2] none) with
  | some (.ite .equal 4 (.reg 6) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp (.wordTest .w64 (.compare .leq))) [1, 2] none) with
  | some (.ite .notLower 6 (.reg 4) (.assign 8 (.const 18)) (.assign 8 (.const 2)), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp (.wordTest .w64 (.compare .gt))) [1, 2] none) with
  | some (.skip, 2) => true
  | _ => false
#guard match compileControl? (width := 8) conf 5 2 (.assign 3 (.blockOp (.cons 15)) [] none) with
  | some (.assign 8 (.const 242), 2) => true
  | _ => false
#guard match compileControl? (width := 8) conf 5 2 (.assign 3 (.blockOp (.cons 16)) [] none) with
  | some (.seq (.assign 1 (.const 255)) (.alloc 1 (.ls (), .ln)), 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_comparisons
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp (.wordOpw .w8 .xor)) [1, 2] none) with
  | some (.assign 8 (.op .xor [.var 4, .var 6]), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp (.wordOpw .w8 .add)) [1, 2] none) with
  | some (.assign 8 (.shift .lsr (.shift .lsl (.op .add [.var 4, .var 6]) (.const 54)) (.const 54)), 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_byte_ops
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp (.wordShift .w8 .lsl 10)) [1] none) with
  | some (.assign 8 (.shift .lsr (.shift .lsl (.var 4) (.const 62)) (.const 54)), 2) => true
  | _ => false
#guard match compileControl? (width := 64) conf 5 2 (.assign 3 (.wordOp (.wordShift .w8 .ror 0)) [1] none) with
  | some (.assign 8 (.op .or [.shift .lsl (.shift .lsr (.var 4) (.const 2)) (.const 2),
      .shift .lsr (.shift .lsl (.var 4) (.const 62)) (.const 54)]), 2) => true
  | _ => false
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_byte_shifts

def runChecks : IO Bool := do
  IO.println "PASS data_to_word shift_length/small_shift_length/get_gen_size match six original HOL rows"
  pure true

end Flapjack.Test.DataToWordConfigParity

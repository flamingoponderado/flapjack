import Flapjack.Compiler.Backend.DataToWord.Config
import Flapjack.Compiler.Backend.DataToWord.Header
import Flapjack.Compiler.Backend.DataToWord.Locations
import Flapjack.Compiler.Backend.DataToWord.WordOp
import Flapjack.Compiler.Backend.DataToWord.Control
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
#guard (compileControl? (width := 64) conf 5 2 (.assign 0 (.intOp .add) [] none)).isNone
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
#guard Flapjack.Test.CakeMLFlatOracle.data_to_word_loads

def runChecks : IO Bool := do
  IO.println "PASS data_to_word shift_length/small_shift_length/get_gen_size match six original HOL rows"
  pure true

end Flapjack.Test.DataToWordConfigParity

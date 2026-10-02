import Flapjack.Compiler.Backend.WordToStack.Proofs.FrameOffsets
import Mathlib.Data.List.Forall2
open Flapjack Flapjack.WordToStackProofs
set_option maxRecDepth 8192

-- fo_suffix_1_1_0
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 1)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_1_1_1
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 1)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_2
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 1)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_3
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_4
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_1_5
example : (absStack ([2] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 1)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_1_6
example : (absStack ([3] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 1)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_7
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_8
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_9
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_10
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 1)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_11
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 1)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_12
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_13
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_1_14
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_15
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_1_16
example : (absStack ([2] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 1)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_1_17
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_1_18
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_1_19
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_1_20
example : (absStack ([0, 255] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_80_0
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 1)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_1_80_1
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 1)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_2
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 1)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_3
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_4
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_80_5
example : (absStack ([2] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 1)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_80_6
example : (absStack ([3] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 1)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_7
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_8
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_9
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_10
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 1)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_11
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 1)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_12
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_13
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_80_14
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_15
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_1_80_16
example : (absStack ([2] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 1)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_80_17
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_80_18
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_80_19
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_1_80_20
example : (absStack ([0, 255] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 1)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_1_0
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 2)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_2_1_1
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 2)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_2
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 2)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_3
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_4
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_1_5
example : (absStack ([2] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 2)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_6
example : (absStack ([3] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 2)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_7
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_8
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_9
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_10
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 2)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_11
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 2)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_12
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_13
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_1_14
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_15
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_16
example : (absStack ([2] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 2)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_1_17
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_1_18
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_1_19
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_1_20
example : (absStack ([0, 255] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_80_0
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 2)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_2_80_1
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 2)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_2
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 2)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_3
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_4
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_80_5
example : (absStack ([2] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 2)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_6
example : (absStack ([3] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 2)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_7
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_8
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_9
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_10
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 2)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_11
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 2)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_12
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_13
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_80_14
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_15
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_16
example : (absStack ([2] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 2)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_2_80_17
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_80_18
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_80_19
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_2_80_20
example : (absStack ([0, 255] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 2)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_1_0
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 8)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_8_1_1
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 8)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_2
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 8)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_3
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_4
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_1_5
example : (absStack ([2] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 8)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_1_6
example : (absStack ([3] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 8)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_1_7
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_8
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_9
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_10
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 8)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_11
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 8)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_12
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_13
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_1_14
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_15
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_1_16
example : (absStack ([2] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 8)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 6, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_1_17
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_1_18
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_1_19
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_1_20
example : (absStack ([0, 255] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_80_0
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 8)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_8_80_1
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 8)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_2
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 8)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_3
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_4
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_80_5
example : (absStack ([2] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 8)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_80_6
example : (absStack ([3] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 8)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_80_7
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_8
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_9
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_10
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 8)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_11
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 8)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_12
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_13
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_80_14
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_15
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_8_80_16
example : (absStack ([2] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 8)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 6, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_80_17
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_80_18
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_80_19
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_8_80_20
example : (absStack ([0, 255] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 8)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_1_0
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 32)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_32_1_1
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 32)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_2
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 32)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_3
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_4
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_1_5
example : (absStack ([2] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 32)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_1_6
example : (absStack ([3] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 32)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_1_7
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_8
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_9
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_10
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 32)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_11
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 32)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_12
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_13
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_1_14
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_15
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_1_16
example : (absStack ([2] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 32)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 6, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_1_17
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_1_18
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_1_19
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_1_20
example : (absStack ([0, 255] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_80_0
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 32)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_32_80_1
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 32)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_2
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 32)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_3
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_4
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_80_5
example : (absStack ([2] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 32)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_80_6
example : (absStack ([3] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 32)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_80_7
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_8
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_9
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_10
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 32)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_11
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 32)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_12
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_13
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_80_14
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_15
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_32_80_16
example : (absStack ([2] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 32)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 6, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_80_17
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_80_18
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_80_19
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_32_80_20
example : (absStack ([0, 255] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 32)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_1_0
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 64)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_64_1_1
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 64)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_2
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 64)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_3
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_4
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_1_5
example : (absStack ([2] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 64)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_1_6
example : (absStack ([3] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 64)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_1_7
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_8
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_9
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_10
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 64)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_11
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 64)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_12
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_13
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_1_14
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_15
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_1_16
example : (absStack ([2] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 64)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 6, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_1_17
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_1_18
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_1_19
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_1_20
example : (absStack ([0, 255] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_80_0
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 64)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_64_80_1
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 64)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_2
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 64)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_3
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_4
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_80_5
example : (absStack ([2] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 64)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_80_6
example : (absStack ([3] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 64)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_80_7
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_8
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_9
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_10
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 64)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_11
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 64)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_12
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_13
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_80_14
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_15
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_64_80_16
example : (absStack ([2] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 64)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 6, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_80_17
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_80_18
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_80_19
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_64_80_20
example : (absStack ([0, 255] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 64)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_1_0
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 80)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_80_1_1
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 80)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_2
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 80)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_3
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_4
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_1_5
example : (absStack ([2] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 80)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_1_6
example : (absStack ([3] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 80)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_1_7
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_8
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_9
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_10
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 80)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_11
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 80)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_12
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_13
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_1_14
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_15
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_1_16
example : (absStack ([2] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 80)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 6, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_1_17
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_1_18
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_1_19
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_1_20
example : (absStack ([0, 255] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_80_0
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 80)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 1, 1, 1] := by
  simp +decide [absStack]

-- fo_suffix_80_80_1
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 80)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_2
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 80)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_3
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_4
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_80_5
example : (absStack ([2] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 80)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_80_6
example : (absStack ([3] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 80)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 3, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_80_7
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_8
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_9
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_10
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 80)) []).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_11
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 80)) [2]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_12
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_13
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 5, 5] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_80_14
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_15
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = none := by
  simp +decide [absStack]

-- fo_suffix_80_80_16
example : (absStack ([2] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 80)) [1]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 6, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_80_17
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 5, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_80_18
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 3, 3] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_80_19
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 6, 6] := by
  simp +decide [absStack]; decide +kernel

-- fo_suffix_80_80_20
example : (absStack ([0, 255] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 80)) [0]).map (fun xs => [0,1,2,99].map (fun n => handlerVal (wordSemLastN n xs))) = some [1, 2, 2, 2] := by
  simp +decide [absStack]; decide +kernel

-- fo_relation_0_0
example : (decide (List.Forall₂ absFrameEq ([] : List (Option Nat × Nat × List Nat)) ([] : List (Option Nat × Nat × List Bool))), handlerVal ([] : List (Option Nat × Nat × List Nat)), handlerVal ([] : List (Option Nat × Nat × List Bool))) = (true, 1, 1) := by decide +kernel

-- fo_relation_0_1
example : (decide (List.Forall₂ absFrameEq ([] : List (Option Nat × Nat × List Nat)) ([(none,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 1, 2) := by decide +kernel

-- fo_relation_0_2
example : (decide (List.Forall₂ absFrameEq ([] : List (Option Nat × Nat × List Nat)) ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 1, 4) := by decide +kernel

-- fo_relation_0_3
example : (decide (List.Forall₂ absFrameEq ([] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 1, 5) := by decide +kernel

-- fo_relation_0_4
example : (decide (List.Forall₂ absFrameEq ([] : List (Option Nat × Nat × List Nat)) ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 1, 7) := by decide +kernel

-- fo_relation_0_5
example : (decide (List.Forall₂ absFrameEq ([] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 1, 9) := by decide +kernel

-- fo_relation_0_6
example : (decide (List.Forall₂ absFrameEq ([] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 1, 9) := by decide +kernel

-- fo_relation_0_7
example : (decide (List.Forall₂ absFrameEq ([] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 1, 10) := by decide +kernel

-- fo_relation_1_0
example : (decide (List.Forall₂ absFrameEq ([(none,0,[])] : List (Option Nat × Nat × List Nat)) ([] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([] : List (Option Nat × Nat × List Bool))) = (false, 2, 1) := by decide +kernel

-- fo_relation_1_1
example : (decide (List.Forall₂ absFrameEq ([(none,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Bool))) = (true, 2, 2) := by decide +kernel

-- fo_relation_1_2
example : (decide (List.Forall₂ absFrameEq ([(none,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 2, 4) := by decide +kernel

-- fo_relation_1_3
example : (decide (List.Forall₂ absFrameEq ([(none,0,[])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 2, 5) := by decide +kernel

-- fo_relation_1_4
example : (decide (List.Forall₂ absFrameEq ([(none,0,[])] : List (Option Nat × Nat × List Nat)) ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 2, 7) := by decide +kernel

-- fo_relation_1_5
example : (decide (List.Forall₂ absFrameEq ([(none,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 2, 9) := by decide +kernel

-- fo_relation_1_6
example : (decide (List.Forall₂ absFrameEq ([(none,0,[])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 2, 9) := by decide +kernel

-- fo_relation_1_7
example : (decide (List.Forall₂ absFrameEq ([(none,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 2, 10) := by decide +kernel

-- fo_relation_2_0
example : (decide (List.Forall₂ absFrameEq ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([] : List (Option Nat × Nat × List Bool))) = (false, 4, 1) := by decide +kernel

-- fo_relation_2_1
example : (decide (List.Forall₂ absFrameEq ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 4, 2) := by decide +kernel

-- fo_relation_2_2
example : (decide (List.Forall₂ absFrameEq ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (true, 4, 4) := by decide +kernel

-- fo_relation_2_3
example : (decide (List.Forall₂ absFrameEq ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 4, 5) := by decide +kernel

-- fo_relation_2_4
example : (decide (List.Forall₂ absFrameEq ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 4, 7) := by decide +kernel

-- fo_relation_2_5
example : (decide (List.Forall₂ absFrameEq ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 4, 9) := by decide +kernel

-- fo_relation_2_6
example : (decide (List.Forall₂ absFrameEq ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 4, 9) := by decide +kernel

-- fo_relation_2_7
example : (decide (List.Forall₂ absFrameEq ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 4, 10) := by decide +kernel

-- fo_relation_3_0
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([] : List (Option Nat × Nat × List Bool))) = (false, 5, 1) := by decide +kernel

-- fo_relation_3_1
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 5, 2) := by decide +kernel

-- fo_relation_3_2
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 5, 4) := by decide +kernel

-- fo_relation_3_3
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (true, 5, 5) := by decide +kernel

-- fo_relation_3_4
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 5, 7) := by decide +kernel

-- fo_relation_3_5
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 5, 9) := by decide +kernel

-- fo_relation_3_6
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 5, 9) := by decide +kernel

-- fo_relation_3_7
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 5, 10) := by decide +kernel

-- fo_relation_4_0
example : (decide (List.Forall₂ absFrameEq ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([] : List (Option Nat × Nat × List Bool))) = (false, 7, 1) := by decide +kernel

-- fo_relation_4_1
example : (decide (List.Forall₂ absFrameEq ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 7, 2) := by decide +kernel

-- fo_relation_4_2
example : (decide (List.Forall₂ absFrameEq ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 7, 4) := by decide +kernel

-- fo_relation_4_3
example : (decide (List.Forall₂ absFrameEq ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 7, 5) := by decide +kernel

-- fo_relation_4_4
example : (decide (List.Forall₂ absFrameEq ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (true, 7, 7) := by decide +kernel

-- fo_relation_4_5
example : (decide (List.Forall₂ absFrameEq ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 7, 9) := by decide +kernel

-- fo_relation_4_6
example : (decide (List.Forall₂ absFrameEq ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 7, 9) := by decide +kernel

-- fo_relation_4_7
example : (decide (List.Forall₂ absFrameEq ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 7, 10) := by decide +kernel

-- fo_relation_5_0
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([] : List (Option Nat × Nat × List Bool))) = (false, 9, 1) := by decide +kernel

-- fo_relation_5_1
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 9, 2) := by decide +kernel

-- fo_relation_5_2
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 9, 4) := by decide +kernel

-- fo_relation_5_3
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 9, 5) := by decide +kernel

-- fo_relation_5_4
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 9, 7) := by decide +kernel

-- fo_relation_5_5
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (true, 9, 9) := by decide +kernel

-- fo_relation_5_6
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 9, 9) := by decide +kernel

-- fo_relation_5_7
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (some 7,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 9, 10) := by decide +kernel

-- fo_relation_6_0
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([] : List (Option Nat × Nat × List Bool))) = (false, 9, 1) := by decide +kernel

-- fo_relation_6_1
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 9, 2) := by decide +kernel

-- fo_relation_6_2
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 9, 4) := by decide +kernel

-- fo_relation_6_3
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 9, 5) := by decide +kernel

-- fo_relation_6_4
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 9, 7) := by decide +kernel

-- fo_relation_6_5
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 9, 9) := by decide +kernel

-- fo_relation_6_6
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (true, 9, 9) := by decide +kernel

-- fo_relation_6_7
example : (decide (List.Forall₂ absFrameEq ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(some 7,0,[11]), (none,1,[11, 12])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 9, 10) := by decide +kernel

-- fo_relation_7_0
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([] : List (Option Nat × Nat × List Bool))) = (false, 10, 1) := by decide +kernel

-- fo_relation_7_1
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 10, 2) := by decide +kernel

-- fo_relation_7_2
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 10, 4) := by decide +kernel

-- fo_relation_7_3
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (false, 10, 5) := by decide +kernel

-- fo_relation_7_4
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 10, 7) := by decide +kernel

-- fo_relation_7_5
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (some 7,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 10, 9) := by decide +kernel

-- fo_relation_7_6
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(some 7,0,[false]), (none,1,[false, true])] : List (Option Nat × Nat × List Bool))) = (false, 10, 9) := by decide +kernel

-- fo_relation_7_7
example : (decide (List.Forall₂ absFrameEq ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)) ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))), handlerVal ([(none,0,[11]), (none,1,[11, 12]), (some 7,0,[])] : List (Option Nat × Nat × List Nat)), handlerVal ([(none,0,[false]), (none,1,[false, true]), (some 7,0,[])] : List (Option Nat × Nat × List Bool))) = (true, 10, 10) := by decide +kernel

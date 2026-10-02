import Flapjack.Compiler.Backend.WordToStack.Proofs.StackAbstractionLength
open Flapjack Flapjack.WordToStackProofs
set_option maxRecDepth 8192

-- asl_case_1_1_0
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 1)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_1
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 1)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_2
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 1)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_3
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_4
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 1)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_5
example : (absStack ([2] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 1)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_6
example : (absStack ([3] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 1)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_7
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_8
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_9
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_10
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 1)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_11
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 1)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_12
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_13
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_14
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_15
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_16
example : (absStack ([2] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 1)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_17
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_18
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_19
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_1_20
example : (absStack ([0, 255] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 1)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_0
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 1)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_1
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 1)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_2
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 1)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_3
example : (absStack ([] : List (BitVec 1)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_4
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 1)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_5
example : (absStack ([2] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 1)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_6
example : (absStack ([3] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 1)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_7
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_8
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_9
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_10
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 1)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_11
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 1)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_12
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_13
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_14
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_15
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 1)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_16
example : (absStack ([2] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 1)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_17
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_18
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_19
example : (absStack ([0] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 1)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_1_80_20
example : (absStack ([0, 255] : List (BitVec 1)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 1)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_0
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 2)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_1
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 2)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_2
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 2)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_3
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_4
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 2)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_5
example : (absStack ([2] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 2)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_6
example : (absStack ([3] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 2)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_7
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_8
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_9
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_10
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 2)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_11
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 2)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_12
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_13
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_14
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_15
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_16
example : (absStack ([2] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 2)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_17
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_18
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_19
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_1_20
example : (absStack ([0, 255] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 2)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_0
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 2)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_1
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 2)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_2
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 2)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_3
example : (absStack ([] : List (BitVec 2)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_4
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 2)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_5
example : (absStack ([2] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 2)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_6
example : (absStack ([3] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 2)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_7
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_8
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_9
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_10
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 2)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_11
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 2)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_12
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_13
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_14
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_15
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 2)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_16
example : (absStack ([2] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 2)) [1]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_17
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_18
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_19
example : (absStack ([0] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 2)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_2_80_20
example : (absStack ([0, 255] : List (BitVec 2)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 2)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_0
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 8)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_1
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 8)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_2
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 8)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_3
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_4
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 8)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_5
example : (absStack ([2] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 8)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_6
example : (absStack ([3] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 8)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_7
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_8
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_9
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_10
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 8)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_11
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 8)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_12
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_13
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_14
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_15
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_16
example : (absStack ([2] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 8)) [1]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_17
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_18
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_19
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_1_20
example : (absStack ([0, 255] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 8)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_0
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 8)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_1
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 8)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_2
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 8)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_3
example : (absStack ([] : List (BitVec 8)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_4
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 8)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_5
example : (absStack ([2] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 8)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_6
example : (absStack ([3] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 8)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_7
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_8
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_9
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_10
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 8)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_11
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 8)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_12
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_13
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_14
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_15
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 8)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_16
example : (absStack ([2] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 8)) [1]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_17
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_18
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_19
example : (absStack ([0] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 8)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_8_80_20
example : (absStack ([0, 255] : List (BitVec 8)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 8)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_0
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 32)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_1
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 32)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_2
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 32)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_3
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_4
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 32)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_5
example : (absStack ([2] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 32)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_6
example : (absStack ([3] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 32)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_7
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_8
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_9
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_10
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 32)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_11
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 32)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_12
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_13
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_14
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_15
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_16
example : (absStack ([2] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 32)) [1]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_17
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_18
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_19
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_1_20
example : (absStack ([0, 255] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 32)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_0
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 32)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_1
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 32)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_2
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 32)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_3
example : (absStack ([] : List (BitVec 32)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_4
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 32)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_5
example : (absStack ([2] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 32)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_6
example : (absStack ([3] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 32)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_7
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_8
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_9
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_10
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 32)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_11
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 32)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_12
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_13
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_14
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_15
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 32)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_16
example : (absStack ([2] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 32)) [1]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_17
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_18
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_19
example : (absStack ([0] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 32)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_32_80_20
example : (absStack ([0, 255] : List (BitVec 32)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 32)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_0
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 64)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_1
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 64)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_2
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 64)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_3
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_4
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 64)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_5
example : (absStack ([2] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 64)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_6
example : (absStack ([3] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 64)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_7
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_8
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_9
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_10
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 64)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_11
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 64)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_12
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_13
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_14
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_15
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_16
example : (absStack ([2] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 64)) [1]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_17
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_18
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_19
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_1_20
example : (absStack ([0, 255] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 64)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_0
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 64)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_1
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 64)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_2
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 64)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_3
example : (absStack ([] : List (BitVec 64)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_4
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 64)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_5
example : (absStack ([2] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 64)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_6
example : (absStack ([3] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 64)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_7
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_8
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_9
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_10
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 64)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_11
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 64)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_12
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_13
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_14
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_15
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 64)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_16
example : (absStack ([2] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 64)) [1]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_17
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_18
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_19
example : (absStack ([0] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 64)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_64_80_20
example : (absStack ([0, 255] : List (BitVec 64)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 64)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_0
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 80)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_1
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 1)) ([] : List (WordLocW 80)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_2
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 80)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_3
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 1)) ([.word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_4
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 80)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_5
example : (absStack ([2] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 80)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_6
example : (absStack ([3] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 80)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_7
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 0, .word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_8
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.loc 2 9, .word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_9
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 4, .word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_10
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 80)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_11
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 7, .word 0] : List (WordLocW 80)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_12
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_13
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_14
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_15
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_16
example : (absStack ([2] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 80)) [1]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_17
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_18
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_19
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_1_20
example : (absStack ([0, 255] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 1)) ([.word 1, .word 0] : List (WordLocW 80)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_0
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 80)) []).map handlerVal = some 1 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_1
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 80)) ([] : List (WordLocW 80)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_2
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 80)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_3
example : (absStack ([] : List (BitVec 80)) ([] : List (WordSemStackFrame 80)) ([.word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_4
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 80)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_5
example : (absStack ([2] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 80)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_6
example : (absStack ([3] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 3 4, .word 0] : List (WordLocW 80)) [1]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_7
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 0, .word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_8
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.loc 2 9, .word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_9
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 4, .word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_10
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 80)) []).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_11
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 7, .word 0] : List (WordLocW 80)) [2]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_12
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_13
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0]).map handlerVal = some 5 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_14
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 2, .loc 1 2, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_15
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7] : List (WordLocW 80)) [0]).map handlerVal = none := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_16
example : (absStack ([2] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .loc 1 2, .word 7, .word 1, .word 9, .word 0] : List (WordLocW 80)) [1]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_17
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43))] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .loc 2 3, .word 7, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_18
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none, .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map handlerVal = some 3 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_19
example : (absStack ([0] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] (some (999,42,43)), .stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .loc 2 3, .word 7, .word 1, .word 1, .word 0] : List (WordLocW 80)) [0, 0]).map handlerVal = some 6 := by
  simp +decide [absStack] <;> decide +kernel

-- asl_case_80_80_20
example : (absStack ([0, 255] : List (BitVec 80)) ([.stackFrame (some 999) [(7,.word 1208925819614629174706175)] [(9,.loc 40 41)] none] : List (WordSemStackFrame 80)) ([.word 1, .word 0] : List (WordLocW 80)) [0]).map handlerVal = some 2 := by
  simp +decide [absStack] <;> decide +kernel


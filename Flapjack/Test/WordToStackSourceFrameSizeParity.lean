import Flapjack.Compiler.Backend.WordToStack.Proofs.SourceFrameSize
open Flapjack Flapjack.WordToStackProofs Flapjack.WordSemStateFiniteExact
set_option maxRecDepth 8192

-- ss_decode_1_0_0_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1, some (some 1)) := by decide +kernel

-- ss_decode_1_0_1_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_1_0_2_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_1_0_3_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_1_0_4_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_1_1_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_1_1_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_1_1_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_1_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_1_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_1_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_1_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_1_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_1_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_1_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_2_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_1_2_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_2_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_1_2_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_1_2_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_1_2_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_2_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_1_2_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_2_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_1_2_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_3_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_3_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_3_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_3_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_3_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_1_3_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_1_3_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_3_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_3_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_3_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_4_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_1_4_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_4_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_1_4_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_4_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_1_4_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_1_4_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_1_4_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_4_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_1_4_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_5_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_5_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_5_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_5_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_5_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_1_5_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_1_5_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_5_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_5_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_1_5_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_6_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_1_6_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_6_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_1_6_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_6_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_1_6_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_6_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_1_6_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_1_6_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_1_6_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_7_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_1_7_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_1_7_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_1_7_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_7_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_1_7_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_7_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_1_7_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_1_7_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_1_7_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_0_0_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1, some (some 1)) := by decide +kernel

-- ss_decode_2_0_1_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_2_0_2_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_2_0_3_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_2_0_4_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_2_1_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_2_1_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_2_1_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_1_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_1_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_1_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_1_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_1_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_1_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_1_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_2_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_2_2_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_2_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_2_2_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_2_2_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_2_2_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_2_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_2_2_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_2_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_2_2_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_3_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_3_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_3_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_3_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_3_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_2_3_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_2_3_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_3_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_3_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_3_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_4_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_2_4_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_4_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_2_4_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_4_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_2_4_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_2_4_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_2_4_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_4_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_2_4_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_5_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_5_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_5_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_5_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_5_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_2_5_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_2_5_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_5_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_5_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_2_5_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_6_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_2_6_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_6_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_2_6_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_6_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_2_6_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_6_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_2_6_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_2_6_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_2_6_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_7_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_2_7_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_2_7_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_2_7_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_7_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_2_7_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_7_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_2_7_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_2_7_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_2_7_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_0_0_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1, some (some 1)) := by decide +kernel

-- ss_decode_8_0_1_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_8_0_2_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_8_0_3_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_8_0_4_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_8_1_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_8_1_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_8_1_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_1_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_1_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_1_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_1_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_1_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_1_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_1_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_2_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_8_2_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_2_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_8_2_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_8_2_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_8_2_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_2_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_8_2_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_2_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_8_2_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_3_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_3_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_3_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_3_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_3_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_8_3_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_8_3_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_3_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_3_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_3_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_4_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_8_4_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_4_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_8_4_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_4_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_8_4_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_8_4_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_8_4_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_4_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_8_4_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_5_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_5_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_5_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_5_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_5_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_8_5_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_8_5_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_5_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_5_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_8_5_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_6_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_8_6_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_6_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_8_6_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_6_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_8_6_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_6_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_8_6_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_8_6_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_8_6_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_7_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_8_7_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_8_7_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_8_7_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_7_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_8_7_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_7_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_8_7_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_8_7_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_8_7_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_0_0_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1, some (some 1)) := by decide +kernel

-- ss_decode_64_0_1_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_64_0_2_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_64_0_3_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_64_0_4_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_64_1_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_64_1_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_64_1_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_1_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_1_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_1_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_1_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_1_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_1_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_1_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_2_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_64_2_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_2_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_64_2_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_64_2_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_64_2_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_2_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_64_2_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_2_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_64_2_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_3_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_3_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_3_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_3_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_3_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_64_3_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_64_3_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_3_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_3_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_3_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_4_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_64_4_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_4_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_64_4_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_4_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_64_4_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_64_4_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_64_4_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_4_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_64_4_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_5_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_5_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_5_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_5_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_5_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_64_5_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_64_5_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_5_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_5_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_64_5_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_6_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_64_6_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_6_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_64_6_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_6_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_64_6_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_6_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_64_6_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_64_6_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_64_6_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_7_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_64_7_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_64_7_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_64_7_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_7_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_64_7_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_7_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_64_7_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_64_7_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_64_7_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_0_0_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1, some (some 1)) := by decide +kernel

-- ss_decode_80_0_1_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_80_0_2_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_80_0_3_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_80_0_4_0
example : (wordSemStackSize ([] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1, none) := by decide +kernel

-- ss_decode_80_1_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_80_1_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_80_1_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_1_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_1_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_1_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_1_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_1_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_1_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_1_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_2_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_80_2_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_2_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_80_2_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_80_2_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_80_2_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_2_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_80_2_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_2_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_80_2_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_3_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_3_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_3_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_3_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_3_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_80_3_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_80_3_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_3_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_3_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_3_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_4_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_80_4_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_4_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_80_4_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_4_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, some (some 1003)) := by decide +kernel

-- ss_decode_80_4_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_80_4_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_80_4_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_4_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1003, none) := by decide +kernel

-- ss_decode_80_4_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_5_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_5_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_5_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_5_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_5_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, some (some 1000)) := by decide +kernel

-- ss_decode_80_5_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_80_5_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_5_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_5_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 1000, none) := by decide +kernel

-- ss_decode_80_5_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_6_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_80_6_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_6_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_80_6_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_6_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_80_6_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_6_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_80_6_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_80_6_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_80_6_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_7_0_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, some (some 2002)) := by decide +kernel

-- ss_decode_80_7_0_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, some (none)) := by decide +kernel

-- ss_decode_80_7_1_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_80_7_1_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_7_2_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_80_7_2_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_7_3_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_80_7_3_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

-- ss_decode_80_7_4_0
example : (wordSemStackSize ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (some 2002, none) := by decide +kernel

-- ss_decode_80_7_4_1
example : (wordSemStackSize ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80)), (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame none [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map wordSemStackSize) = (none, none) := by decide +kernel

private def base {width : Nat} [NeZero width] : WordSemStateFiniteExact width Unit Unit where
  locals := .ln
  localsSize := none
  fpRegs := HolFiniteMapExact.empty
  store := HolFiniteMapExact.empty
  stack := []
  stackLimit := 0
  stackMax := none
  stackSize := .ln
  memory := fun _ => .word 0
  mdomain := fun _ => false
  shMdomain := fun _ => false
  permute := fun _ i => i
  compile := fun _ _ => none
  compileOracle := fun _ => ((), [])
  codeBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  dataBuffer := { position := 0, buffer := [], spaceLeft := 0 }
  gcFun := fun _ => none
  handler := 0
  clock := 0
  termdep := 0
  code := .ln
  be := false
  ffi := { oracle := fun _ state _ _ => .ret state [], ffiState := (), ioEvents := [] }

private def frameView {width : Nat} [NeZero width] : WordSemStackFrame width →
    Option Nat × List (Nat × WordLocW width) × List (Nat × WordLocW width) × Option (Nat × Nat × Nat)
  | .stackFrame n l0 l h => (n,l0,l,h)

-- ss_push_1_0_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 1 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], none, none, none, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_1_0_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 1 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], none, none, none, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_1_1_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 1 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 0, some 6, some 6, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_1_1_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 1 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 0, some 9, some 9, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_1_2_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 1 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 2, some 8, some 8, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_1_2_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 1 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 2, some 11, some 11, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_2_0_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 2 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], none, none, none, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_2_0_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 2 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], none, none, none, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_2_1_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 2 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 0, some 6, some 6, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_2_1_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 2 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 0, some 9, some 9, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_2_2_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 2 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 2, some 8, some 8, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_2_2_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 2 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 2, some 11, some 11, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_8_0_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 8 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], none, none, none, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_8_0_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 8 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], none, none, none, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_8_1_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 8 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 0, some 6, some 6, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_8_1_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 8 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 0, some 9, some 9, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_8_2_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 8 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 2, some 8, some 8, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_8_2_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 8 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 2, some 11, some 11, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_64_0_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 64 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], none, none, none, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_64_0_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 64 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], none, none, none, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_64_1_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 64 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 0, some 6, some 6, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_64_1_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 64 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 0, some 9, some 9, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_64_2_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 64 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 2, some 8, some 8, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_64_2_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 64 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 2, some 11, some 11, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_80_0_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 80 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], none, none, none, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_80_0_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 80 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := none, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(none,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], none, none, none, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_80_1_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 80 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 0, some 6, some 6, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_80_1_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 80 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 0, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 0,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 0, some 9, some 9, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_80_2_0
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) none (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 80 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],none),(some 2,[],[],some (11,12,13))], some 2, some 8, some 8, 9, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

-- ss_push_80_2_1
example : let t := pushEnv (sptInsert 4 (.word 5) .ln, sptInsert 3 (.loc 1 2) .ln) (some (99,.skip,7,8)) (setStore .allocSize (.word 42) { (base : WordSemStateFiniteExact 80 Unit Unit) with stack := [.stackFrame (some 2) [] [] (some (11,12,13))], localsSize := some 2, handler := 9, stackMax := some 4 })
    (t.stack.map frameView, t.localsSize, wordSemStackSize t.stack, t.stackMax, t.handler, t.store.lookup .allocSize) =
    ([(some 2,[(4,.word 5)],[(3,.loc 1 2)],some (9,7,8)),(some 2,[],[],some (11,12,13))], some 2, some 11, some 11, 1, some (.word 42)) := by
  simp [pushEnv, setStore, base, frameView, wordSemStackSize, wordSemStackSizeFrame, wordSemOptionAdd, wordSemEnvToList, wordSemListRearrange, wordSemOptionMax, FUPDATE_HOL]
  decide +kernel

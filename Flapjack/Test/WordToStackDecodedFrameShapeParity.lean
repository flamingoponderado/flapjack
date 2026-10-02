import Flapjack.Compiler.Backend.WordToStack.Proofs.DecodedFrameShape
open Flapjack Flapjack.WordToStackProofs
set_option maxRecDepth 8192

-- dfs_handler_1_0_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = some [] := by decide +kernel

-- dfs_sorted_1_0_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_1_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_1_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_1_1_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_1_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_1_1_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 1) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 1)).map Prod.fst |>.zip ([] : List (WordLocW 1))) none) = true := by decide +kernel

-- dfs_handler_1_2_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_2_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_1_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_1_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_1_2_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43)) : WordSemStackFrame 1) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1)] : List (Nat × WordLocW 1)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 1))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_1_3_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_3_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_1_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_1_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_1_3_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none : WordSemStackFrame 1) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 1)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 1))) none) = true := by decide +kernel

-- dfs_handler_1_4_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_4_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_1_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_1_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_1_4_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 1) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (3,.word 2)] : List (Nat × WordLocW 1)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 1))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_1_5_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_5_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_1_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_1_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_1_5_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none : WordSemStackFrame 1) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (5,.word 2)] : List (Nat × WordLocW 1)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 1))) none) = true := by decide +kernel

-- dfs_handler_1_6_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_6_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = some [true, false] := by decide +kernel

-- dfs_sorted_1_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_1_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_1_6_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 1) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 1)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 1))) (some (999,42,43))) = true := by decide +kernel

-- dfs_zip_1_6_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none : WordSemStackFrame 1) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(9,.word 1)] : List (Nat × WordLocW 1)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 1))) none) = true := by decide +kernel

-- dfs_handler_1_7_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = some [false, true] := by decide +kernel

-- dfs_sorted_1_7_0
example : (wordSemDecStack ([] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_1_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_1_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_1_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 1)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 1))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_1_7_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 1) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 1)).map Prod.fst |>.zip ([] : List (WordLocW 1))) none) = true := by decide +kernel

-- dfs_zip_1_7_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43)) : WordSemStackFrame 1) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 1)).map Prod.fst |>.zip ([] : List (WordLocW 1))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_2_0_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = some [] := by decide +kernel

-- dfs_sorted_2_0_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_2_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_1_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_2_1_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_2_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_2_1_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 2) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 2)).map Prod.fst |>.zip ([] : List (WordLocW 2))) none) = true := by decide +kernel

-- dfs_handler_2_2_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_2_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_2_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_2_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_2_2_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43)) : WordSemStackFrame 2) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1)] : List (Nat × WordLocW 2)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 2))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_2_3_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_3_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_2_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_2_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_2_3_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none : WordSemStackFrame 2) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 2)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 2))) none) = true := by decide +kernel

-- dfs_handler_2_4_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_4_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_2_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_2_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_2_4_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 2) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (3,.word 2)] : List (Nat × WordLocW 2)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 2))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_2_5_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_5_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_2_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_2_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_2_5_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none : WordSemStackFrame 2) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (5,.word 2)] : List (Nat × WordLocW 2)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 2))) none) = true := by decide +kernel

-- dfs_handler_2_6_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_6_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = some [true, false] := by decide +kernel

-- dfs_sorted_2_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_2_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_2_6_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 2) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 2)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 2))) (some (999,42,43))) = true := by decide +kernel

-- dfs_zip_2_6_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none : WordSemStackFrame 2) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(9,.word 1)] : List (Nat × WordLocW 2)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 2))) none) = true := by decide +kernel

-- dfs_handler_2_7_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = some [false, true] := by decide +kernel

-- dfs_sorted_2_7_0
example : (wordSemDecStack ([] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_2_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_2_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_2_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 2)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 2))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_2_7_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 2) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 2)).map Prod.fst |>.zip ([] : List (WordLocW 2))) none) = true := by decide +kernel

-- dfs_zip_2_7_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43)) : WordSemStackFrame 2) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 2)).map Prod.fst |>.zip ([] : List (WordLocW 2))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_8_0_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = some [] := by decide +kernel

-- dfs_sorted_8_0_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_8_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_1_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_8_1_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_8_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_8_1_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 8) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 8)).map Prod.fst |>.zip ([] : List (WordLocW 8))) none) = true := by decide +kernel

-- dfs_handler_8_2_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_2_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_8_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_8_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_8_2_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43)) : WordSemStackFrame 8) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1)] : List (Nat × WordLocW 8)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 8))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_8_3_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_3_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_8_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_8_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_8_3_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none : WordSemStackFrame 8) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 8)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 8))) none) = true := by decide +kernel

-- dfs_handler_8_4_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_4_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_8_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_8_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_8_4_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 8) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (3,.word 2)] : List (Nat × WordLocW 8)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 8))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_8_5_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_5_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_8_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_8_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_8_5_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none : WordSemStackFrame 8) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (5,.word 2)] : List (Nat × WordLocW 8)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 8))) none) = true := by decide +kernel

-- dfs_handler_8_6_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_6_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = some [true, false] := by decide +kernel

-- dfs_sorted_8_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_8_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_8_6_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 8) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 8)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 8))) (some (999,42,43))) = true := by decide +kernel

-- dfs_zip_8_6_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none : WordSemStackFrame 8) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(9,.word 1)] : List (Nat × WordLocW 8)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 8))) none) = true := by decide +kernel

-- dfs_handler_8_7_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = some [false, true] := by decide +kernel

-- dfs_sorted_8_7_0
example : (wordSemDecStack ([] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_8_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_8_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_8_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 8)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 8))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_8_7_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 8) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 8)).map Prod.fst |>.zip ([] : List (WordLocW 8))) none) = true := by decide +kernel

-- dfs_zip_8_7_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43)) : WordSemStackFrame 8) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 8)).map Prod.fst |>.zip ([] : List (WordLocW 8))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_64_0_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = some [] := by decide +kernel

-- dfs_sorted_64_0_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_64_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_1_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_64_1_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_64_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_64_1_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 64) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 64)).map Prod.fst |>.zip ([] : List (WordLocW 64))) none) = true := by decide +kernel

-- dfs_handler_64_2_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_2_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_64_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_64_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_64_2_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43)) : WordSemStackFrame 64) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1)] : List (Nat × WordLocW 64)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 64))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_64_3_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_3_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_64_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_64_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_64_3_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none : WordSemStackFrame 64) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 64)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 64))) none) = true := by decide +kernel

-- dfs_handler_64_4_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_4_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_64_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_64_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_64_4_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 64) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (3,.word 2)] : List (Nat × WordLocW 64)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 64))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_64_5_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_5_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_64_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_64_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_64_5_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none : WordSemStackFrame 64) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (5,.word 2)] : List (Nat × WordLocW 64)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 64))) none) = true := by decide +kernel

-- dfs_handler_64_6_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_6_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = some [true, false] := by decide +kernel

-- dfs_sorted_64_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_64_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_64_6_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 64) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 64)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 64))) (some (999,42,43))) = true := by decide +kernel

-- dfs_zip_64_6_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none : WordSemStackFrame 64) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(9,.word 1)] : List (Nat × WordLocW 64)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 64))) none) = true := by decide +kernel

-- dfs_handler_64_7_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = some [false, true] := by decide +kernel

-- dfs_sorted_64_7_0
example : (wordSemDecStack ([] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_64_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_64_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_64_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 64)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 64))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_64_7_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 64) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 64)).map Prod.fst |>.zip ([] : List (WordLocW 64))) none) = true := by decide +kernel

-- dfs_zip_64_7_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43)) : WordSemStackFrame 64) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 64)).map Prod.fst |>.zip ([] : List (WordLocW 64))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_80_0_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = some [] := by decide +kernel

-- dfs_sorted_80_0_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_80_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_0_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_0_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_0_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_0_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_1_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_80_1_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_80_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_1_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_1_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_1_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_1_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_80_1_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 80) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 80)).map Prod.fst |>.zip ([] : List (WordLocW 80))) none) = true := by decide +kernel

-- dfs_handler_80_2_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_2_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_80_2_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_80_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_2_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_2_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_2_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_80_2_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1)] (some (999,42,43)) : WordSemStackFrame 80) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1)] : List (Nat × WordLocW 80)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 80))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_80_3_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_3_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_3_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_80_3_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_80_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_3_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_3_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_80_3_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] none : WordSemStackFrame 80) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 80)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 80))) none) = true := by decide +kernel

-- dfs_handler_80_4_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_4_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_4_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = some [true] := by decide +kernel

-- dfs_sorted_80_4_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_80_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_4_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_4_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_80_4_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 80) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (3,.word 2)] : List (Nat × WordLocW 80)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 80))) (some (999,42,43))) = true := by decide +kernel

-- dfs_handler_80_5_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_5_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_5_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = some [false] := by decide +kernel

-- dfs_sorted_80_5_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = some false := by decide +kernel

-- dfs_handler_80_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_5_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_5_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_80_5_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(3,.word 1), (5,.word 2)] none : WordSemStackFrame 80) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(3,.word 1), (5,.word 2)] : List (Nat × WordLocW 80)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 80))) none) = true := by decide +kernel

-- dfs_handler_80_6_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_6_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_6_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_6_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = some [true, false] := by decide +kernel

-- dfs_sorted_80_6_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_80_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_6_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)), .stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_80_6_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(5,.word 1), (3,.word 2)] (some (999,42,43)) : WordSemStackFrame 80) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(5,.word 1), (3,.word 2)] : List (Nat × WordLocW 80)).map Prod.fst |>.zip ([.word 41, .word 42] : List (WordLocW 80))) (some (999,42,43))) = true := by decide +kernel

-- dfs_zip_80_6_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [(9,.word 1)] none : WordSemStackFrame 80) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([(9,.word 1)] : List (Nat × WordLocW 80)).map Prod.fst |>.zip ([.word 41] : List (WordLocW 80))) none) = true := by decide +kernel

-- dfs_handler_80_7_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = some [false, true] := by decide +kernel

-- dfs_sorted_80_7_0
example : (wordSemDecStack ([] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = some true := by decide +kernel

-- dfs_handler_80_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_7_1
example : (wordSemDecStack ([.word 41] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_7_2
example : (wordSemDecStack ([.word 41, .word 42] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_7_3
example : (wordSemDecStack ([.word 41, .word 42, .word 43] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_handler_80_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.map isHandlerFrame) = none := by decide +kernel

-- dfs_sorted_80_7_4
example : (wordSemDecStack ([.word 41, .word 42, .word 43, .word 44] : List (WordLocW 80)) ([.stackFrame (some 999) [(7,.loc 40 41)] [] none, .stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43))] : List (WordSemStackFrame 80))).map (fun xs => xs.all sortedEnv) = none := by decide +kernel

-- dfs_zip_80_7_0
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] none : WordSemStackFrame 80) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 80)).map Prod.fst |>.zip ([] : List (WordLocW 80))) none) = true := by decide +kernel

-- dfs_zip_80_7_1
example : sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] [] (some (999,42,43)) : WordSemStackFrame 80) = true → sortedEnv (.stackFrame (some 999) [(7,.loc 40 41)] (([] : List (Nat × WordLocW 80)).map Prod.fst |>.zip ([] : List (WordLocW 80))) (some (999,42,43))) = true := by decide +kernel


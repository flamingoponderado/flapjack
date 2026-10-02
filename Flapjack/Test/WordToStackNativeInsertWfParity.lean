import Flapjack.Compiler.Backend.WordToStack.Proofs.NativeInsertWf
open Flapjack Flapjack.WordToStackProofs
-- iw_insert_num_0_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_num_0_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_num_0_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_num_0_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_num_0_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_num_0_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) .ln)) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_0_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) .ln)) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_0_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) .ln)) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_0_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_num_0_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) .ln)) = ((.bn (.ls 3) .ln), true, true) := by decide +kernel

-- iw_insert_num_0_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) .ln)) = ((.bs (.ls 3) 9 .ln), true, true) := by decide +kernel

-- iw_insert_num_0_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) .ln)) = ((.bs (.ls 3) 9 .ln), true, true) := by decide +kernel

-- iw_insert_num_0_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_num_0_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) .ln)) = ((.bn .ln (.bn .ln (.bn .ln (.ls 3)))), true, true) := by decide +kernel

-- iw_insert_num_0_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) .ln)) = ((.bn .ln (.bs .ln 9 (.bn .ln (.ls 3)))), true, true) := by decide +kernel

-- iw_insert_num_0_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) .ln, sptWf (.ln:Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) .ln)) = ((.bs (.bn .ln (.bn .ln (.ls 9))) 13 (.bs .ln 9 (.bs .ln 3 (.ls 3)))), true, true) := by decide +kernel

-- iw_insert_num_1_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) (.ls 3))) = ((.bs (.ls 3) 3 .ln), true, true) := by decide +kernel

-- iw_insert_num_1_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) (.ls 3))) = ((.bs (.ls 3) 9 .ln), true, true) := by decide +kernel

-- iw_insert_num_1_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) (.ls 3))) = ((.bs (.ls 3) 9 .ln), true, true) := by decide +kernel

-- iw_insert_num_1_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) (.ls 3))) = ((.ls 3), true, true) := by decide +kernel

-- iw_insert_num_1_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) (.ls 3))) = ((.bs .ln 3 (.bn .ln (.bn .ln (.ls 3)))), true, true) := by decide +kernel

-- iw_insert_num_1_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) (.ls 3))) = ((.bs .ln 3 (.bs .ln 9 (.bn .ln (.ls 3)))), true, true) := by decide +kernel

-- iw_insert_num_1_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) (.ls 3), sptWf ((.ls 3):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) (.ls 3))) = ((.bs (.bn .ln (.bn .ln (.ls 9))) 13 (.bs .ln 9 (.bs .ln 3 (.ls 3)))), true, true) := by decide +kernel

-- iw_insert_num_2_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_num_2_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_num_2_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_num_2_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_num_2_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_num_2_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) (.bn .ln .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_2_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) (.bn .ln .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_2_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) (.bn .ln .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_2_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_num_2_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) (.bn .ln .ln))) = ((.bn (.ls 3) .ln), false, true) := by decide +kernel

-- iw_insert_num_2_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) (.bn .ln .ln))) = ((.bs (.ls 3) 9 .ln), false, true) := by decide +kernel

-- iw_insert_num_2_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) (.bn .ln .ln))) = ((.bs (.ls 3) 9 .ln), false, true) := by decide +kernel

-- iw_insert_num_2_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_num_2_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) (.bn .ln .ln))) = ((.bn .ln (.bn .ln (.bn .ln (.ls 3)))), false, true) := by decide +kernel

-- iw_insert_num_2_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) (.bn .ln .ln))) = ((.bn .ln (.bs .ln 9 (.bn .ln (.ls 3)))), false, true) := by decide +kernel

-- iw_insert_num_2_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) (.bn .ln .ln))) = ((.bs (.bn .ln (.bn .ln (.ls 9))) 13 (.bs .ln 9 (.bs .ln 3 (.ls 3)))), false, true) := by decide +kernel

-- iw_insert_num_3_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) (.bs .ln 3 .ln))) = ((.bs (.ls 3) 3 .ln), false, true) := by decide +kernel

-- iw_insert_num_3_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) (.bs .ln 3 .ln))) = ((.bs (.ls 3) 9 .ln), false, true) := by decide +kernel

-- iw_insert_num_3_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) (.bs .ln 3 .ln))) = ((.bs (.ls 3) 9 .ln), false, true) := by decide +kernel

-- iw_insert_num_3_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 .ln), false, false) := by decide +kernel

-- iw_insert_num_3_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 (.bn .ln (.bn .ln (.ls 3)))), false, true) := by decide +kernel

-- iw_insert_num_3_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) (.bs .ln 3 .ln))) = ((.bs .ln 3 (.bs .ln 9 (.bn .ln (.ls 3)))), false, true) := by decide +kernel

-- iw_insert_num_3_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) (.bs .ln 3 .ln), sptWf ((.bs .ln 3 .ln):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) (.bs .ln 3 .ln))) = ((.bs (.bn .ln (.bn .ln (.ls 9))) 13 (.bs .ln 9 (.bs .ln 3 (.ls 3)))), false, true) := by decide +kernel

-- iw_insert_num_4_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([3,9,13,9,3]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([3,9,13,9,3]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 3) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 3) 9 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([3,9,13,9,3]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 3) 9 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.ls 13)), true, true) := by decide +kernel

-- iw_insert_num_4_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.bs .ln 13 (.bn .ln (.ls 3)))), true, true) := by decide +kernel

-- iw_insert_num_4_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.ls 9) 3 (.bs .ln 9 (.bn .ln (.ls 3)))), true, true) := by decide +kernel

-- iw_insert_num_4_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) (.bs (.ls 9) 3 (.ls 13)), sptWf ((.bs (.ls 9) 3 (.ls 13)):Spt Nat), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([3,9,13,9,3]:List Nat) (.bs (.ls 9) 3 (.ls 13)))) = ((.bs (.bs .ln 9 (.bn .ln (.ls 9))) 13 (.bs .ln 9 (.bs .ln 3 (.ls 3)))), true, true) := by decide +kernel

-- iw_fromlist_num_0
example : (sptFromList2 ([]:List Nat), sptWf (sptFromList2 ([]:List Nat))) = (.ln, true) := by decide +kernel

-- iw_fromlist_num_1
example : (sptFromList2 ([3]:List Nat), sptWf (sptFromList2 ([3]:List Nat))) = ((.ls 3), true) := by decide +kernel

-- iw_fromlist_num_2
example : (sptFromList2 ([3,9]:List Nat), sptWf (sptFromList2 ([3,9]:List Nat))) = ((.bs (.ls 9) 3 .ln), true) := by decide +kernel

-- iw_fromlist_num_3
example : (sptFromList2 ([3,9,13,9,3]:List Nat), sptWf (sptFromList2 ([3,9,13,9,3]:List Nat))) = ((.bs (.bs (.ls 9) 9 (.bs .ln 13 (.ls 3))) 3 .ln), true) := by decide +kernel

-- iw_insert_bool_0_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_bool_0_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_bool_0_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_bool_0_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_bool_0_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_bool_0_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) .ln)) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_0_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) .ln)) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_0_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) .ln)) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_0_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_bool_0_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) .ln)) = ((.bn (.ls true) .ln), true, true) := by decide +kernel

-- iw_insert_bool_0_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) .ln)) = ((.bs (.ls true) false .ln), true, true) := by decide +kernel

-- iw_insert_bool_0_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) .ln)) = ((.bs (.ls true) false .ln), true, true) := by decide +kernel

-- iw_insert_bool_0_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) .ln)) = (.ln, true, true) := by decide +kernel

-- iw_insert_bool_0_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) .ln)) = ((.bn .ln (.bn .ln (.bn .ln (.ls true)))), true, true) := by decide +kernel

-- iw_insert_bool_0_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) .ln)) = ((.bn .ln (.bs .ln false (.bn .ln (.ls true)))), true, true) := by decide +kernel

-- iw_insert_bool_0_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) .ln, sptWf (.ln:Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) .ln)) = ((.bs (.bn .ln (.bn .ln (.ls false))) true (.bs .ln false (.bs .ln true (.ls true)))), true, true) := by decide +kernel

-- iw_insert_bool_1_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) (.ls true))) = ((.bs (.ls true) true .ln), true, true) := by decide +kernel

-- iw_insert_bool_1_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) (.ls true))) = ((.bs (.ls true) false .ln), true, true) := by decide +kernel

-- iw_insert_bool_1_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) (.ls true))) = ((.bs (.ls true) false .ln), true, true) := by decide +kernel

-- iw_insert_bool_1_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) (.ls true))) = ((.ls true), true, true) := by decide +kernel

-- iw_insert_bool_1_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) (.ls true))) = ((.bs .ln true (.bn .ln (.bn .ln (.ls true)))), true, true) := by decide +kernel

-- iw_insert_bool_1_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) (.ls true))) = ((.bs .ln true (.bs .ln false (.bn .ln (.ls true)))), true, true) := by decide +kernel

-- iw_insert_bool_1_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) (.ls true), sptWf ((.ls true):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) (.ls true))) = ((.bs (.bn .ln (.bn .ln (.ls false))) true (.bs .ln false (.bs .ln true (.ls true)))), true, true) := by decide +kernel

-- iw_insert_bool_2_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) (.bn .ln .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) (.bn .ln .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) (.bn .ln .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) (.bn .ln .ln))) = ((.bn (.ls true) .ln), false, true) := by decide +kernel

-- iw_insert_bool_2_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) (.bn .ln .ln))) = ((.bs (.ls true) false .ln), false, true) := by decide +kernel

-- iw_insert_bool_2_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) (.bn .ln .ln))) = ((.bs (.ls true) false .ln), false, true) := by decide +kernel

-- iw_insert_bool_2_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) (.bn .ln .ln))) = ((.bn .ln .ln), false, false) := by decide +kernel

-- iw_insert_bool_2_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) (.bn .ln .ln))) = ((.bn .ln (.bn .ln (.bn .ln (.ls true)))), false, true) := by decide +kernel

-- iw_insert_bool_2_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) (.bn .ln .ln))) = ((.bn .ln (.bs .ln false (.bn .ln (.ls true)))), false, true) := by decide +kernel

-- iw_insert_bool_2_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) (.bn .ln .ln), sptWf ((.bn .ln .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) (.bn .ln .ln))) = ((.bs (.bn .ln (.bn .ln (.ls false))) true (.bs .ln false (.bs .ln true (.ls true)))), false, true) := by decide +kernel

-- iw_insert_bool_3_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) (.bs .ln true .ln))) = ((.bs (.ls true) true .ln), false, true) := by decide +kernel

-- iw_insert_bool_3_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) (.bs .ln true .ln))) = ((.bs (.ls true) false .ln), false, true) := by decide +kernel

-- iw_insert_bool_3_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) (.bs .ln true .ln))) = ((.bs (.ls true) false .ln), false, true) := by decide +kernel

-- iw_insert_bool_3_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true .ln), false, false) := by decide +kernel

-- iw_insert_bool_3_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true (.bn .ln (.bn .ln (.ls true)))), false, true) := by decide +kernel

-- iw_insert_bool_3_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) (.bs .ln true .ln))) = ((.bs .ln true (.bs .ln false (.bn .ln (.ls true)))), false, true) := by decide +kernel

-- iw_insert_bool_3_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) (.bs .ln true .ln), sptWf ((.bs .ln true .ln):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) (.bs .ln true .ln))) = ((.bs (.bn .ln (.bn .ln (.ls false))) true (.bs .ln false (.bs .ln true (.ls true)))), false, true) := by decide +kernel

-- iw_insert_bool_4_0_0
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_0_1
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_0_2
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_0_3
example : (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [] ([true,false,true,false,true]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_1_0
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_1_1
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_1_2
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_1_3
example : (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [0] ([true,false,true,false,true]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_2_0
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_2_1
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls true) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_2_2
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls true) false (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_2_3
example : (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [2,0,2] ([true,false,true,false,true]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls true) false (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_3_0
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.ls true)), true, true) := by decide +kernel

-- iw_insert_bool_4_3_1
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.bs .ln true (.bn .ln (.ls true)))), true, true) := by decide +kernel

-- iw_insert_bool_4_3_2
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.ls false) true (.bs .ln false (.bn .ln (.ls true)))), true, true) := by decide +kernel

-- iw_insert_bool_4_3_3
example : (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) (.bs (.ls false) true (.ls true)), sptWf ((.bs (.ls false) true (.ls true)):Spt Bool), sptWf (LoopSemStateFiniteExact.sptAlistInsert [7,1,0,8,3] ([true,false,true,false,true]:List Bool) (.bs (.ls false) true (.ls true)))) = ((.bs (.bs .ln false (.bn .ln (.ls false))) true (.bs .ln false (.bs .ln true (.ls true)))), true, true) := by decide +kernel

-- iw_fromlist_bool_0
example : (sptFromList2 ([]:List Bool), sptWf (sptFromList2 ([]:List Bool))) = (.ln, true) := by decide +kernel

-- iw_fromlist_bool_1
example : (sptFromList2 ([true]:List Bool), sptWf (sptFromList2 ([true]:List Bool))) = ((.ls true), true) := by decide +kernel

-- iw_fromlist_bool_2
example : (sptFromList2 ([true,false]:List Bool), sptWf (sptFromList2 ([true,false]:List Bool))) = ((.bs (.ls false) true .ln), true) := by decide +kernel

-- iw_fromlist_bool_3
example : (sptFromList2 ([true,false,true,false,true]:List Bool), sptWf (sptFromList2 ([true,false,true,false,true]:List Bool))) = ((.bs (.bs (.ls false) false (.bs .ln true (.ls true))) true .ln), true) := by decide +kernel

example {α : Type} (xs : List Nat) (ys : List α) (z : Spt α) (h : sptWf z = true) : sptWf (LoopSemStateFiniteExact.sptAlistInsert xs ys z) = true := wfAlistInsert xs ys z h
example {α : Type} (ls : List α) : sptWf (sptFromList2 ls) = true := wfFromList2 ls

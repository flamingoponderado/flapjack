import Flapjack.Compiler.Backend.WordToStack.Proofs.StackSuffix
open Flapjack Flapjack.WordToStackProofs
set_option maxRecDepth 8192

-- sl_suffix_Nat_0_0
example : (wordSemLastN 0 ([] : List Nat), (wordSemLastN 0 ([] : List Nat)).length, decide ((wordSemLastN 0 ([] : List Nat)).length ≤ 0), decide ((wordSemLastN 0 ([] : List Nat)).length ≤ 0), (wordSemLastN 0 ([] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_0_0
example : (wordSemLastN (0+1) ([] : List Nat), (wordSemLastN (0+1) ([] : List Nat)).tail, wordSemLastN 0 ([] : List Nat), decide (0+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_suffix_Nat_0_1
example : (wordSemLastN 1 ([] : List Nat), (wordSemLastN 1 ([] : List Nat)).length, decide ((wordSemLastN 1 ([] : List Nat)).length ≤ 1), decide ((wordSemLastN 1 ([] : List Nat)).length ≤ 0), (wordSemLastN 1 ([] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_0_1
example : (wordSemLastN (1+1) ([] : List Nat), (wordSemLastN (1+1) ([] : List Nat)).tail, wordSemLastN 1 ([] : List Nat), decide (1+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_suffix_Nat_0_2
example : (wordSemLastN 2 ([] : List Nat), (wordSemLastN 2 ([] : List Nat)).length, decide ((wordSemLastN 2 ([] : List Nat)).length ≤ 2), decide ((wordSemLastN 2 ([] : List Nat)).length ≤ 0), (wordSemLastN 2 ([] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_0_2
example : (wordSemLastN (2+1) ([] : List Nat), (wordSemLastN (2+1) ([] : List Nat)).tail, wordSemLastN 2 ([] : List Nat), decide (2+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_suffix_Nat_0_99
example : (wordSemLastN 99 ([] : List Nat), (wordSemLastN 99 ([] : List Nat)).length, decide ((wordSemLastN 99 ([] : List Nat)).length ≤ 99), decide ((wordSemLastN 99 ([] : List Nat)).length ≤ 0), (wordSemLastN 99 ([] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_0_99
example : (wordSemLastN (99+1) ([] : List Nat), (wordSemLastN (99+1) ([] : List Nat)).tail, wordSemLastN 99 ([] : List Nat), decide (99+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_suffix_Nat_0_900
example : (wordSemLastN 900 ([] : List Nat), (wordSemLastN 900 ([] : List Nat)).length, decide ((wordSemLastN 900 ([] : List Nat)).length ≤ 900), decide ((wordSemLastN 900 ([] : List Nat)).length ≤ 0), (wordSemLastN 900 ([] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_0_900
example : (wordSemLastN (900+1) ([] : List Nat), (wordSemLastN (900+1) ([] : List Nat)).tail, wordSemLastN 900 ([] : List Nat), decide (900+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_cons_Nat_0_0
example : wordSemLastN (0+1) (0::([] : List Nat)) = [0] := by decide +kernel

-- sl_cons_Nat_0_99
example : wordSemLastN (0+1) (99::([] : List Nat)) = [99] := by decide +kernel

-- sl_suffix_Nat_1_0
example : (wordSemLastN 0 ([0] : List Nat), (wordSemLastN 0 ([0] : List Nat)).length, decide ((wordSemLastN 0 ([0] : List Nat)).length ≤ 0), decide ((wordSemLastN 0 ([0] : List Nat)).length ≤ 1), (wordSemLastN 0 ([0] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_1_0
example : (wordSemLastN (0+1) ([0] : List Nat), (wordSemLastN (0+1) ([0] : List Nat)).tail, wordSemLastN 0 ([0] : List Nat), decide (0+1 ≤ 1)) = ([0], [], [], true) := by decide +kernel

-- sl_suffix_Nat_1_1
example : (wordSemLastN 1 ([0] : List Nat), (wordSemLastN 1 ([0] : List Nat)).length, decide ((wordSemLastN 1 ([0] : List Nat)).length ≤ 1), decide ((wordSemLastN 1 ([0] : List Nat)).length ≤ 1), (wordSemLastN 1 ([0] : List Nat)).all (fun x => decide (x%2=0))) = ([0], 1, true, true, true) := by decide +kernel

-- sl_less_Nat_1_1
example : (wordSemLastN (1+1) ([0] : List Nat), (wordSemLastN (1+1) ([0] : List Nat)).tail, wordSemLastN 1 ([0] : List Nat), decide (1+1 ≤ 1)) = ([0], [], [0], false) := by decide +kernel

-- sl_suffix_Nat_1_2
example : (wordSemLastN 2 ([0] : List Nat), (wordSemLastN 2 ([0] : List Nat)).length, decide ((wordSemLastN 2 ([0] : List Nat)).length ≤ 2), decide ((wordSemLastN 2 ([0] : List Nat)).length ≤ 1), (wordSemLastN 2 ([0] : List Nat)).all (fun x => decide (x%2=0))) = ([0], 1, true, true, true) := by decide +kernel

-- sl_less_Nat_1_2
example : (wordSemLastN (2+1) ([0] : List Nat), (wordSemLastN (2+1) ([0] : List Nat)).tail, wordSemLastN 2 ([0] : List Nat), decide (2+1 ≤ 1)) = ([0], [], [0], false) := by decide +kernel

-- sl_suffix_Nat_1_3
example : (wordSemLastN 3 ([0] : List Nat), (wordSemLastN 3 ([0] : List Nat)).length, decide ((wordSemLastN 3 ([0] : List Nat)).length ≤ 3), decide ((wordSemLastN 3 ([0] : List Nat)).length ≤ 1), (wordSemLastN 3 ([0] : List Nat)).all (fun x => decide (x%2=0))) = ([0], 1, true, true, true) := by decide +kernel

-- sl_less_Nat_1_3
example : (wordSemLastN (3+1) ([0] : List Nat), (wordSemLastN (3+1) ([0] : List Nat)).tail, wordSemLastN 3 ([0] : List Nat), decide (3+1 ≤ 1)) = ([0], [], [0], false) := by decide +kernel

-- sl_suffix_Nat_1_99
example : (wordSemLastN 99 ([0] : List Nat), (wordSemLastN 99 ([0] : List Nat)).length, decide ((wordSemLastN 99 ([0] : List Nat)).length ≤ 99), decide ((wordSemLastN 99 ([0] : List Nat)).length ≤ 1), (wordSemLastN 99 ([0] : List Nat)).all (fun x => decide (x%2=0))) = ([0], 1, true, true, true) := by decide +kernel

-- sl_less_Nat_1_99
example : (wordSemLastN (99+1) ([0] : List Nat), (wordSemLastN (99+1) ([0] : List Nat)).tail, wordSemLastN 99 ([0] : List Nat), decide (99+1 ≤ 1)) = ([0], [], [0], false) := by decide +kernel

-- sl_suffix_Nat_1_900
example : (wordSemLastN 900 ([0] : List Nat), (wordSemLastN 900 ([0] : List Nat)).length, decide ((wordSemLastN 900 ([0] : List Nat)).length ≤ 900), decide ((wordSemLastN 900 ([0] : List Nat)).length ≤ 1), (wordSemLastN 900 ([0] : List Nat)).all (fun x => decide (x%2=0))) = ([0], 1, true, true, true) := by decide +kernel

-- sl_less_Nat_1_900
example : (wordSemLastN (900+1) ([0] : List Nat), (wordSemLastN (900+1) ([0] : List Nat)).tail, wordSemLastN 900 ([0] : List Nat), decide (900+1 ≤ 1)) = ([0], [], [0], false) := by decide +kernel

-- sl_head_Nat_1
example : (wordSemLastN 1 ([0] : List Nat), ([0] : List Nat).head (by simp) :: wordSemLastN 0 ([0] : List Nat)) = ([0], [0]) := by decide +kernel

-- sl_cons_Nat_1_0
example : wordSemLastN (1+1) (0::([0] : List Nat)) = [0, 0] := by decide +kernel

-- sl_cons_Nat_1_99
example : wordSemLastN (1+1) (99::([0] : List Nat)) = [99, 0] := by decide +kernel

-- sl_suffix_Nat_2_0
example : (wordSemLastN 0 ([9] : List Nat), (wordSemLastN 0 ([9] : List Nat)).length, decide ((wordSemLastN 0 ([9] : List Nat)).length ≤ 0), decide ((wordSemLastN 0 ([9] : List Nat)).length ≤ 1), (wordSemLastN 0 ([9] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_2_0
example : (wordSemLastN (0+1) ([9] : List Nat), (wordSemLastN (0+1) ([9] : List Nat)).tail, wordSemLastN 0 ([9] : List Nat), decide (0+1 ≤ 1)) = ([9], [], [], true) := by decide +kernel

-- sl_suffix_Nat_2_1
example : (wordSemLastN 1 ([9] : List Nat), (wordSemLastN 1 ([9] : List Nat)).length, decide ((wordSemLastN 1 ([9] : List Nat)).length ≤ 1), decide ((wordSemLastN 1 ([9] : List Nat)).length ≤ 1), (wordSemLastN 1 ([9] : List Nat)).all (fun x => decide (x%2=0))) = ([9], 1, true, true, false) := by decide +kernel

-- sl_less_Nat_2_1
example : (wordSemLastN (1+1) ([9] : List Nat), (wordSemLastN (1+1) ([9] : List Nat)).tail, wordSemLastN 1 ([9] : List Nat), decide (1+1 ≤ 1)) = ([9], [], [9], false) := by decide +kernel

-- sl_suffix_Nat_2_2
example : (wordSemLastN 2 ([9] : List Nat), (wordSemLastN 2 ([9] : List Nat)).length, decide ((wordSemLastN 2 ([9] : List Nat)).length ≤ 2), decide ((wordSemLastN 2 ([9] : List Nat)).length ≤ 1), (wordSemLastN 2 ([9] : List Nat)).all (fun x => decide (x%2=0))) = ([9], 1, true, true, false) := by decide +kernel

-- sl_less_Nat_2_2
example : (wordSemLastN (2+1) ([9] : List Nat), (wordSemLastN (2+1) ([9] : List Nat)).tail, wordSemLastN 2 ([9] : List Nat), decide (2+1 ≤ 1)) = ([9], [], [9], false) := by decide +kernel

-- sl_suffix_Nat_2_3
example : (wordSemLastN 3 ([9] : List Nat), (wordSemLastN 3 ([9] : List Nat)).length, decide ((wordSemLastN 3 ([9] : List Nat)).length ≤ 3), decide ((wordSemLastN 3 ([9] : List Nat)).length ≤ 1), (wordSemLastN 3 ([9] : List Nat)).all (fun x => decide (x%2=0))) = ([9], 1, true, true, false) := by decide +kernel

-- sl_less_Nat_2_3
example : (wordSemLastN (3+1) ([9] : List Nat), (wordSemLastN (3+1) ([9] : List Nat)).tail, wordSemLastN 3 ([9] : List Nat), decide (3+1 ≤ 1)) = ([9], [], [9], false) := by decide +kernel

-- sl_suffix_Nat_2_99
example : (wordSemLastN 99 ([9] : List Nat), (wordSemLastN 99 ([9] : List Nat)).length, decide ((wordSemLastN 99 ([9] : List Nat)).length ≤ 99), decide ((wordSemLastN 99 ([9] : List Nat)).length ≤ 1), (wordSemLastN 99 ([9] : List Nat)).all (fun x => decide (x%2=0))) = ([9], 1, true, true, false) := by decide +kernel

-- sl_less_Nat_2_99
example : (wordSemLastN (99+1) ([9] : List Nat), (wordSemLastN (99+1) ([9] : List Nat)).tail, wordSemLastN 99 ([9] : List Nat), decide (99+1 ≤ 1)) = ([9], [], [9], false) := by decide +kernel

-- sl_suffix_Nat_2_900
example : (wordSemLastN 900 ([9] : List Nat), (wordSemLastN 900 ([9] : List Nat)).length, decide ((wordSemLastN 900 ([9] : List Nat)).length ≤ 900), decide ((wordSemLastN 900 ([9] : List Nat)).length ≤ 1), (wordSemLastN 900 ([9] : List Nat)).all (fun x => decide (x%2=0))) = ([9], 1, true, true, false) := by decide +kernel

-- sl_less_Nat_2_900
example : (wordSemLastN (900+1) ([9] : List Nat), (wordSemLastN (900+1) ([9] : List Nat)).tail, wordSemLastN 900 ([9] : List Nat), decide (900+1 ≤ 1)) = ([9], [], [9], false) := by decide +kernel

-- sl_head_Nat_2
example : (wordSemLastN 1 ([9] : List Nat), ([9] : List Nat).head (by simp) :: wordSemLastN 0 ([9] : List Nat)) = ([9], [9]) := by decide +kernel

-- sl_cons_Nat_2_0
example : wordSemLastN (1+1) (0::([9] : List Nat)) = [0, 9] := by decide +kernel

-- sl_cons_Nat_2_99
example : wordSemLastN (1+1) (99::([9] : List Nat)) = [99, 9] := by decide +kernel

-- sl_suffix_Nat_3_0
example : (wordSemLastN 0 ([1, 2] : List Nat), (wordSemLastN 0 ([1, 2] : List Nat)).length, decide ((wordSemLastN 0 ([1, 2] : List Nat)).length ≤ 0), decide ((wordSemLastN 0 ([1, 2] : List Nat)).length ≤ 2), (wordSemLastN 0 ([1, 2] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_3_0
example : (wordSemLastN (0+1) ([1, 2] : List Nat), (wordSemLastN (0+1) ([1, 2] : List Nat)).tail, wordSemLastN 0 ([1, 2] : List Nat), decide (0+1 ≤ 2)) = ([2], [], [], true) := by decide +kernel

-- sl_suffix_Nat_3_1
example : (wordSemLastN 1 ([1, 2] : List Nat), (wordSemLastN 1 ([1, 2] : List Nat)).length, decide ((wordSemLastN 1 ([1, 2] : List Nat)).length ≤ 1), decide ((wordSemLastN 1 ([1, 2] : List Nat)).length ≤ 2), (wordSemLastN 1 ([1, 2] : List Nat)).all (fun x => decide (x%2=0))) = ([2], 1, true, true, true) := by decide +kernel

-- sl_less_Nat_3_1
example : (wordSemLastN (1+1) ([1, 2] : List Nat), (wordSemLastN (1+1) ([1, 2] : List Nat)).tail, wordSemLastN 1 ([1, 2] : List Nat), decide (1+1 ≤ 2)) = ([1, 2], [2], [2], true) := by decide +kernel

-- sl_suffix_Nat_3_2
example : (wordSemLastN 2 ([1, 2] : List Nat), (wordSemLastN 2 ([1, 2] : List Nat)).length, decide ((wordSemLastN 2 ([1, 2] : List Nat)).length ≤ 2), decide ((wordSemLastN 2 ([1, 2] : List Nat)).length ≤ 2), (wordSemLastN 2 ([1, 2] : List Nat)).all (fun x => decide (x%2=0))) = ([1, 2], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_3_2
example : (wordSemLastN (2+1) ([1, 2] : List Nat), (wordSemLastN (2+1) ([1, 2] : List Nat)).tail, wordSemLastN 2 ([1, 2] : List Nat), decide (2+1 ≤ 2)) = ([1, 2], [2], [1, 2], false) := by decide +kernel

-- sl_suffix_Nat_3_3
example : (wordSemLastN 3 ([1, 2] : List Nat), (wordSemLastN 3 ([1, 2] : List Nat)).length, decide ((wordSemLastN 3 ([1, 2] : List Nat)).length ≤ 3), decide ((wordSemLastN 3 ([1, 2] : List Nat)).length ≤ 2), (wordSemLastN 3 ([1, 2] : List Nat)).all (fun x => decide (x%2=0))) = ([1, 2], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_3_3
example : (wordSemLastN (3+1) ([1, 2] : List Nat), (wordSemLastN (3+1) ([1, 2] : List Nat)).tail, wordSemLastN 3 ([1, 2] : List Nat), decide (3+1 ≤ 2)) = ([1, 2], [2], [1, 2], false) := by decide +kernel

-- sl_suffix_Nat_3_4
example : (wordSemLastN 4 ([1, 2] : List Nat), (wordSemLastN 4 ([1, 2] : List Nat)).length, decide ((wordSemLastN 4 ([1, 2] : List Nat)).length ≤ 4), decide ((wordSemLastN 4 ([1, 2] : List Nat)).length ≤ 2), (wordSemLastN 4 ([1, 2] : List Nat)).all (fun x => decide (x%2=0))) = ([1, 2], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_3_4
example : (wordSemLastN (4+1) ([1, 2] : List Nat), (wordSemLastN (4+1) ([1, 2] : List Nat)).tail, wordSemLastN 4 ([1, 2] : List Nat), decide (4+1 ≤ 2)) = ([1, 2], [2], [1, 2], false) := by decide +kernel

-- sl_suffix_Nat_3_99
example : (wordSemLastN 99 ([1, 2] : List Nat), (wordSemLastN 99 ([1, 2] : List Nat)).length, decide ((wordSemLastN 99 ([1, 2] : List Nat)).length ≤ 99), decide ((wordSemLastN 99 ([1, 2] : List Nat)).length ≤ 2), (wordSemLastN 99 ([1, 2] : List Nat)).all (fun x => decide (x%2=0))) = ([1, 2], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_3_99
example : (wordSemLastN (99+1) ([1, 2] : List Nat), (wordSemLastN (99+1) ([1, 2] : List Nat)).tail, wordSemLastN 99 ([1, 2] : List Nat), decide (99+1 ≤ 2)) = ([1, 2], [2], [1, 2], false) := by decide +kernel

-- sl_suffix_Nat_3_900
example : (wordSemLastN 900 ([1, 2] : List Nat), (wordSemLastN 900 ([1, 2] : List Nat)).length, decide ((wordSemLastN 900 ([1, 2] : List Nat)).length ≤ 900), decide ((wordSemLastN 900 ([1, 2] : List Nat)).length ≤ 2), (wordSemLastN 900 ([1, 2] : List Nat)).all (fun x => decide (x%2=0))) = ([1, 2], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_3_900
example : (wordSemLastN (900+1) ([1, 2] : List Nat), (wordSemLastN (900+1) ([1, 2] : List Nat)).tail, wordSemLastN 900 ([1, 2] : List Nat), decide (900+1 ≤ 2)) = ([1, 2], [2], [1, 2], false) := by decide +kernel

-- sl_head_Nat_3
example : (wordSemLastN 2 ([1, 2] : List Nat), ([1, 2] : List Nat).head (by simp) :: wordSemLastN 1 ([1, 2] : List Nat)) = ([1, 2], [1, 2]) := by decide +kernel

-- sl_cons_Nat_3_0
example : wordSemLastN (2+1) (0::([1, 2] : List Nat)) = [0, 1, 2] := by decide +kernel

-- sl_cons_Nat_3_99
example : wordSemLastN (2+1) (99::([1, 2] : List Nat)) = [99, 1, 2] := by decide +kernel

-- sl_suffix_Nat_4_0
example : (wordSemLastN 0 ([9, 9] : List Nat), (wordSemLastN 0 ([9, 9] : List Nat)).length, decide ((wordSemLastN 0 ([9, 9] : List Nat)).length ≤ 0), decide ((wordSemLastN 0 ([9, 9] : List Nat)).length ≤ 2), (wordSemLastN 0 ([9, 9] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_4_0
example : (wordSemLastN (0+1) ([9, 9] : List Nat), (wordSemLastN (0+1) ([9, 9] : List Nat)).tail, wordSemLastN 0 ([9, 9] : List Nat), decide (0+1 ≤ 2)) = ([9], [], [], true) := by decide +kernel

-- sl_suffix_Nat_4_1
example : (wordSemLastN 1 ([9, 9] : List Nat), (wordSemLastN 1 ([9, 9] : List Nat)).length, decide ((wordSemLastN 1 ([9, 9] : List Nat)).length ≤ 1), decide ((wordSemLastN 1 ([9, 9] : List Nat)).length ≤ 2), (wordSemLastN 1 ([9, 9] : List Nat)).all (fun x => decide (x%2=0))) = ([9], 1, true, true, false) := by decide +kernel

-- sl_less_Nat_4_1
example : (wordSemLastN (1+1) ([9, 9] : List Nat), (wordSemLastN (1+1) ([9, 9] : List Nat)).tail, wordSemLastN 1 ([9, 9] : List Nat), decide (1+1 ≤ 2)) = ([9, 9], [9], [9], true) := by decide +kernel

-- sl_suffix_Nat_4_2
example : (wordSemLastN 2 ([9, 9] : List Nat), (wordSemLastN 2 ([9, 9] : List Nat)).length, decide ((wordSemLastN 2 ([9, 9] : List Nat)).length ≤ 2), decide ((wordSemLastN 2 ([9, 9] : List Nat)).length ≤ 2), (wordSemLastN 2 ([9, 9] : List Nat)).all (fun x => decide (x%2=0))) = ([9, 9], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_4_2
example : (wordSemLastN (2+1) ([9, 9] : List Nat), (wordSemLastN (2+1) ([9, 9] : List Nat)).tail, wordSemLastN 2 ([9, 9] : List Nat), decide (2+1 ≤ 2)) = ([9, 9], [9], [9, 9], false) := by decide +kernel

-- sl_suffix_Nat_4_3
example : (wordSemLastN 3 ([9, 9] : List Nat), (wordSemLastN 3 ([9, 9] : List Nat)).length, decide ((wordSemLastN 3 ([9, 9] : List Nat)).length ≤ 3), decide ((wordSemLastN 3 ([9, 9] : List Nat)).length ≤ 2), (wordSemLastN 3 ([9, 9] : List Nat)).all (fun x => decide (x%2=0))) = ([9, 9], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_4_3
example : (wordSemLastN (3+1) ([9, 9] : List Nat), (wordSemLastN (3+1) ([9, 9] : List Nat)).tail, wordSemLastN 3 ([9, 9] : List Nat), decide (3+1 ≤ 2)) = ([9, 9], [9], [9, 9], false) := by decide +kernel

-- sl_suffix_Nat_4_4
example : (wordSemLastN 4 ([9, 9] : List Nat), (wordSemLastN 4 ([9, 9] : List Nat)).length, decide ((wordSemLastN 4 ([9, 9] : List Nat)).length ≤ 4), decide ((wordSemLastN 4 ([9, 9] : List Nat)).length ≤ 2), (wordSemLastN 4 ([9, 9] : List Nat)).all (fun x => decide (x%2=0))) = ([9, 9], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_4_4
example : (wordSemLastN (4+1) ([9, 9] : List Nat), (wordSemLastN (4+1) ([9, 9] : List Nat)).tail, wordSemLastN 4 ([9, 9] : List Nat), decide (4+1 ≤ 2)) = ([9, 9], [9], [9, 9], false) := by decide +kernel

-- sl_suffix_Nat_4_99
example : (wordSemLastN 99 ([9, 9] : List Nat), (wordSemLastN 99 ([9, 9] : List Nat)).length, decide ((wordSemLastN 99 ([9, 9] : List Nat)).length ≤ 99), decide ((wordSemLastN 99 ([9, 9] : List Nat)).length ≤ 2), (wordSemLastN 99 ([9, 9] : List Nat)).all (fun x => decide (x%2=0))) = ([9, 9], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_4_99
example : (wordSemLastN (99+1) ([9, 9] : List Nat), (wordSemLastN (99+1) ([9, 9] : List Nat)).tail, wordSemLastN 99 ([9, 9] : List Nat), decide (99+1 ≤ 2)) = ([9, 9], [9], [9, 9], false) := by decide +kernel

-- sl_suffix_Nat_4_900
example : (wordSemLastN 900 ([9, 9] : List Nat), (wordSemLastN 900 ([9, 9] : List Nat)).length, decide ((wordSemLastN 900 ([9, 9] : List Nat)).length ≤ 900), decide ((wordSemLastN 900 ([9, 9] : List Nat)).length ≤ 2), (wordSemLastN 900 ([9, 9] : List Nat)).all (fun x => decide (x%2=0))) = ([9, 9], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_4_900
example : (wordSemLastN (900+1) ([9, 9] : List Nat), (wordSemLastN (900+1) ([9, 9] : List Nat)).tail, wordSemLastN 900 ([9, 9] : List Nat), decide (900+1 ≤ 2)) = ([9, 9], [9], [9, 9], false) := by decide +kernel

-- sl_head_Nat_4
example : (wordSemLastN 2 ([9, 9] : List Nat), ([9, 9] : List Nat).head (by simp) :: wordSemLastN 1 ([9, 9] : List Nat)) = ([9, 9], [9, 9]) := by decide +kernel

-- sl_cons_Nat_4_0
example : wordSemLastN (2+1) (0::([9, 9] : List Nat)) = [0, 9, 9] := by decide +kernel

-- sl_cons_Nat_4_99
example : wordSemLastN (2+1) (99::([9, 9] : List Nat)) = [99, 9, 9] := by decide +kernel

-- sl_suffix_Nat_5_0
example : (wordSemLastN 0 ([30, 20, 10] : List Nat), (wordSemLastN 0 ([30, 20, 10] : List Nat)).length, decide ((wordSemLastN 0 ([30, 20, 10] : List Nat)).length ≤ 0), decide ((wordSemLastN 0 ([30, 20, 10] : List Nat)).length ≤ 3), (wordSemLastN 0 ([30, 20, 10] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_5_0
example : (wordSemLastN (0+1) ([30, 20, 10] : List Nat), (wordSemLastN (0+1) ([30, 20, 10] : List Nat)).tail, wordSemLastN 0 ([30, 20, 10] : List Nat), decide (0+1 ≤ 3)) = ([10], [], [], true) := by decide +kernel

-- sl_suffix_Nat_5_1
example : (wordSemLastN 1 ([30, 20, 10] : List Nat), (wordSemLastN 1 ([30, 20, 10] : List Nat)).length, decide ((wordSemLastN 1 ([30, 20, 10] : List Nat)).length ≤ 1), decide ((wordSemLastN 1 ([30, 20, 10] : List Nat)).length ≤ 3), (wordSemLastN 1 ([30, 20, 10] : List Nat)).all (fun x => decide (x%2=0))) = ([10], 1, true, true, true) := by decide +kernel

-- sl_less_Nat_5_1
example : (wordSemLastN (1+1) ([30, 20, 10] : List Nat), (wordSemLastN (1+1) ([30, 20, 10] : List Nat)).tail, wordSemLastN 1 ([30, 20, 10] : List Nat), decide (1+1 ≤ 3)) = ([20, 10], [10], [10], true) := by decide +kernel

-- sl_suffix_Nat_5_2
example : (wordSemLastN 2 ([30, 20, 10] : List Nat), (wordSemLastN 2 ([30, 20, 10] : List Nat)).length, decide ((wordSemLastN 2 ([30, 20, 10] : List Nat)).length ≤ 2), decide ((wordSemLastN 2 ([30, 20, 10] : List Nat)).length ≤ 3), (wordSemLastN 2 ([30, 20, 10] : List Nat)).all (fun x => decide (x%2=0))) = ([20, 10], 2, true, true, true) := by decide +kernel

-- sl_less_Nat_5_2
example : (wordSemLastN (2+1) ([30, 20, 10] : List Nat), (wordSemLastN (2+1) ([30, 20, 10] : List Nat)).tail, wordSemLastN 2 ([30, 20, 10] : List Nat), decide (2+1 ≤ 3)) = ([30, 20, 10], [20, 10], [20, 10], true) := by decide +kernel

-- sl_suffix_Nat_5_3
example : (wordSemLastN 3 ([30, 20, 10] : List Nat), (wordSemLastN 3 ([30, 20, 10] : List Nat)).length, decide ((wordSemLastN 3 ([30, 20, 10] : List Nat)).length ≤ 3), decide ((wordSemLastN 3 ([30, 20, 10] : List Nat)).length ≤ 3), (wordSemLastN 3 ([30, 20, 10] : List Nat)).all (fun x => decide (x%2=0))) = ([30, 20, 10], 3, true, true, true) := by decide +kernel

-- sl_less_Nat_5_3
example : (wordSemLastN (3+1) ([30, 20, 10] : List Nat), (wordSemLastN (3+1) ([30, 20, 10] : List Nat)).tail, wordSemLastN 3 ([30, 20, 10] : List Nat), decide (3+1 ≤ 3)) = ([30, 20, 10], [20, 10], [30, 20, 10], false) := by decide +kernel

-- sl_suffix_Nat_5_4
example : (wordSemLastN 4 ([30, 20, 10] : List Nat), (wordSemLastN 4 ([30, 20, 10] : List Nat)).length, decide ((wordSemLastN 4 ([30, 20, 10] : List Nat)).length ≤ 4), decide ((wordSemLastN 4 ([30, 20, 10] : List Nat)).length ≤ 3), (wordSemLastN 4 ([30, 20, 10] : List Nat)).all (fun x => decide (x%2=0))) = ([30, 20, 10], 3, true, true, true) := by decide +kernel

-- sl_less_Nat_5_4
example : (wordSemLastN (4+1) ([30, 20, 10] : List Nat), (wordSemLastN (4+1) ([30, 20, 10] : List Nat)).tail, wordSemLastN 4 ([30, 20, 10] : List Nat), decide (4+1 ≤ 3)) = ([30, 20, 10], [20, 10], [30, 20, 10], false) := by decide +kernel

-- sl_suffix_Nat_5_5
example : (wordSemLastN 5 ([30, 20, 10] : List Nat), (wordSemLastN 5 ([30, 20, 10] : List Nat)).length, decide ((wordSemLastN 5 ([30, 20, 10] : List Nat)).length ≤ 5), decide ((wordSemLastN 5 ([30, 20, 10] : List Nat)).length ≤ 3), (wordSemLastN 5 ([30, 20, 10] : List Nat)).all (fun x => decide (x%2=0))) = ([30, 20, 10], 3, true, true, true) := by decide +kernel

-- sl_less_Nat_5_5
example : (wordSemLastN (5+1) ([30, 20, 10] : List Nat), (wordSemLastN (5+1) ([30, 20, 10] : List Nat)).tail, wordSemLastN 5 ([30, 20, 10] : List Nat), decide (5+1 ≤ 3)) = ([30, 20, 10], [20, 10], [30, 20, 10], false) := by decide +kernel

-- sl_suffix_Nat_5_99
example : (wordSemLastN 99 ([30, 20, 10] : List Nat), (wordSemLastN 99 ([30, 20, 10] : List Nat)).length, decide ((wordSemLastN 99 ([30, 20, 10] : List Nat)).length ≤ 99), decide ((wordSemLastN 99 ([30, 20, 10] : List Nat)).length ≤ 3), (wordSemLastN 99 ([30, 20, 10] : List Nat)).all (fun x => decide (x%2=0))) = ([30, 20, 10], 3, true, true, true) := by decide +kernel

-- sl_less_Nat_5_99
example : (wordSemLastN (99+1) ([30, 20, 10] : List Nat), (wordSemLastN (99+1) ([30, 20, 10] : List Nat)).tail, wordSemLastN 99 ([30, 20, 10] : List Nat), decide (99+1 ≤ 3)) = ([30, 20, 10], [20, 10], [30, 20, 10], false) := by decide +kernel

-- sl_suffix_Nat_5_900
example : (wordSemLastN 900 ([30, 20, 10] : List Nat), (wordSemLastN 900 ([30, 20, 10] : List Nat)).length, decide ((wordSemLastN 900 ([30, 20, 10] : List Nat)).length ≤ 900), decide ((wordSemLastN 900 ([30, 20, 10] : List Nat)).length ≤ 3), (wordSemLastN 900 ([30, 20, 10] : List Nat)).all (fun x => decide (x%2=0))) = ([30, 20, 10], 3, true, true, true) := by decide +kernel

-- sl_less_Nat_5_900
example : (wordSemLastN (900+1) ([30, 20, 10] : List Nat), (wordSemLastN (900+1) ([30, 20, 10] : List Nat)).tail, wordSemLastN 900 ([30, 20, 10] : List Nat), decide (900+1 ≤ 3)) = ([30, 20, 10], [20, 10], [30, 20, 10], false) := by decide +kernel

-- sl_head_Nat_5
example : (wordSemLastN 3 ([30, 20, 10] : List Nat), ([30, 20, 10] : List Nat).head (by simp) :: wordSemLastN 2 ([30, 20, 10] : List Nat)) = ([30, 20, 10], [30, 20, 10]) := by decide +kernel

-- sl_cons_Nat_5_0
example : wordSemLastN (3+1) (0::([30, 20, 10] : List Nat)) = [0, 30, 20, 10] := by decide +kernel

-- sl_cons_Nat_5_99
example : wordSemLastN (3+1) (99::([30, 20, 10] : List Nat)) = [99, 30, 20, 10] := by decide +kernel

-- sl_suffix_Nat_6_0
example : (wordSemLastN 0 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN 0 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length, decide ((wordSemLastN 0 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 0), decide ((wordSemLastN 0 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), (wordSemLastN 0 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).all (fun x => decide (x%2=0))) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Nat_6_0
example : (wordSemLastN (0+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN (0+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).tail, wordSemLastN 0 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), decide (0+1 ≤ 12)) = ([11], [], [], true) := by decide +kernel

-- sl_suffix_Nat_6_1
example : (wordSemLastN 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length, decide ((wordSemLastN 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 1), decide ((wordSemLastN 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), (wordSemLastN 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).all (fun x => decide (x%2=0))) = ([11], 1, true, true, false) := by decide +kernel

-- sl_less_Nat_6_1
example : (wordSemLastN (1+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN (1+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).tail, wordSemLastN 1 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), decide (1+1 ≤ 12)) = ([10, 11], [11], [11], true) := by decide +kernel

-- sl_suffix_Nat_6_2
example : (wordSemLastN 2 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN 2 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length, decide ((wordSemLastN 2 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 2), decide ((wordSemLastN 2 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), (wordSemLastN 2 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).all (fun x => decide (x%2=0))) = ([10, 11], 2, true, true, false) := by decide +kernel

-- sl_less_Nat_6_2
example : (wordSemLastN (2+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN (2+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).tail, wordSemLastN 2 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), decide (2+1 ≤ 12)) = ([9, 10, 11], [10, 11], [10, 11], true) := by decide +kernel

-- sl_suffix_Nat_6_11
example : (wordSemLastN 11 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN 11 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length, decide ((wordSemLastN 11 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 11), decide ((wordSemLastN 11 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), (wordSemLastN 11 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).all (fun x => decide (x%2=0))) = ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 11, true, true, false) := by decide +kernel

-- sl_less_Nat_6_11
example : (wordSemLastN (11+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN (11+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).tail, wordSemLastN 11 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), decide (11+1 ≤ 12)) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], true) := by decide +kernel

-- sl_suffix_Nat_6_12
example : (wordSemLastN 12 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN 12 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length, decide ((wordSemLastN 12 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), decide ((wordSemLastN 12 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), (wordSemLastN 12 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).all (fun x => decide (x%2=0))) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 12, true, true, false) := by decide +kernel

-- sl_less_Nat_6_12
example : (wordSemLastN (12+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN (12+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).tail, wordSemLastN 12 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), decide (12+1 ≤ 12)) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], false) := by decide +kernel

-- sl_suffix_Nat_6_13
example : (wordSemLastN 13 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN 13 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length, decide ((wordSemLastN 13 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 13), decide ((wordSemLastN 13 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), (wordSemLastN 13 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).all (fun x => decide (x%2=0))) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 12, true, true, false) := by decide +kernel

-- sl_less_Nat_6_13
example : (wordSemLastN (13+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN (13+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).tail, wordSemLastN 13 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), decide (13+1 ≤ 12)) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], false) := by decide +kernel

-- sl_suffix_Nat_6_14
example : (wordSemLastN 14 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN 14 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length, decide ((wordSemLastN 14 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 14), decide ((wordSemLastN 14 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), (wordSemLastN 14 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).all (fun x => decide (x%2=0))) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 12, true, true, false) := by decide +kernel

-- sl_less_Nat_6_14
example : (wordSemLastN (14+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN (14+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).tail, wordSemLastN 14 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), decide (14+1 ≤ 12)) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], false) := by decide +kernel

-- sl_suffix_Nat_6_99
example : (wordSemLastN 99 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN 99 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length, decide ((wordSemLastN 99 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 99), decide ((wordSemLastN 99 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), (wordSemLastN 99 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).all (fun x => decide (x%2=0))) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 12, true, true, false) := by decide +kernel

-- sl_less_Nat_6_99
example : (wordSemLastN (99+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN (99+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).tail, wordSemLastN 99 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), decide (99+1 ≤ 12)) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], false) := by decide +kernel

-- sl_suffix_Nat_6_900
example : (wordSemLastN 900 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN 900 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length, decide ((wordSemLastN 900 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 900), decide ((wordSemLastN 900 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).length ≤ 12), (wordSemLastN 900 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).all (fun x => decide (x%2=0))) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 12, true, true, false) := by decide +kernel

-- sl_less_Nat_6_900
example : (wordSemLastN (900+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), (wordSemLastN (900+1) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)).tail, wordSemLastN 900 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), decide (900+1 ≤ 12)) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], false) := by decide +kernel

-- sl_head_Nat_6
example : (wordSemLastN 12 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat), ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat).head (by simp) :: wordSemLastN 11 ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)) = ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) := by decide +kernel

-- sl_cons_Nat_6_0
example : wordSemLastN (12+1) (0::([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)) = [0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by decide +kernel

-- sl_cons_Nat_6_99
example : wordSemLastN (12+1) (99::([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] : List Nat)) = [99, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11] := by decide +kernel

-- sl_suffix_Bool_0_0
example : (wordSemLastN 0 ([] : List Bool), (wordSemLastN 0 ([] : List Bool)).length, decide ((wordSemLastN 0 ([] : List Bool)).length ≤ 0), decide ((wordSemLastN 0 ([] : List Bool)).length ≤ 0), (wordSemLastN 0 ([] : List Bool)).all id) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Bool_0_0
example : (wordSemLastN (0+1) ([] : List Bool), (wordSemLastN (0+1) ([] : List Bool)).tail, wordSemLastN 0 ([] : List Bool), decide (0+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_suffix_Bool_0_1
example : (wordSemLastN 1 ([] : List Bool), (wordSemLastN 1 ([] : List Bool)).length, decide ((wordSemLastN 1 ([] : List Bool)).length ≤ 1), decide ((wordSemLastN 1 ([] : List Bool)).length ≤ 0), (wordSemLastN 1 ([] : List Bool)).all id) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Bool_0_1
example : (wordSemLastN (1+1) ([] : List Bool), (wordSemLastN (1+1) ([] : List Bool)).tail, wordSemLastN 1 ([] : List Bool), decide (1+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_suffix_Bool_0_2
example : (wordSemLastN 2 ([] : List Bool), (wordSemLastN 2 ([] : List Bool)).length, decide ((wordSemLastN 2 ([] : List Bool)).length ≤ 2), decide ((wordSemLastN 2 ([] : List Bool)).length ≤ 0), (wordSemLastN 2 ([] : List Bool)).all id) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Bool_0_2
example : (wordSemLastN (2+1) ([] : List Bool), (wordSemLastN (2+1) ([] : List Bool)).tail, wordSemLastN 2 ([] : List Bool), decide (2+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_suffix_Bool_0_99
example : (wordSemLastN 99 ([] : List Bool), (wordSemLastN 99 ([] : List Bool)).length, decide ((wordSemLastN 99 ([] : List Bool)).length ≤ 99), decide ((wordSemLastN 99 ([] : List Bool)).length ≤ 0), (wordSemLastN 99 ([] : List Bool)).all id) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Bool_0_99
example : (wordSemLastN (99+1) ([] : List Bool), (wordSemLastN (99+1) ([] : List Bool)).tail, wordSemLastN 99 ([] : List Bool), decide (99+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_suffix_Bool_0_900
example : (wordSemLastN 900 ([] : List Bool), (wordSemLastN 900 ([] : List Bool)).length, decide ((wordSemLastN 900 ([] : List Bool)).length ≤ 900), decide ((wordSemLastN 900 ([] : List Bool)).length ≤ 0), (wordSemLastN 900 ([] : List Bool)).all id) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Bool_0_900
example : (wordSemLastN (900+1) ([] : List Bool), (wordSemLastN (900+1) ([] : List Bool)).tail, wordSemLastN 900 ([] : List Bool), decide (900+1 ≤ 0)) = ([], [], [], false) := by decide +kernel

-- sl_cons_Bool_0_0
example : wordSemLastN (0+1) (false::([] : List Bool)) = [false] := by decide +kernel

-- sl_cons_Bool_0_1
example : wordSemLastN (0+1) (true::([] : List Bool)) = [true] := by decide +kernel

-- sl_suffix_Bool_1_0
example : (wordSemLastN 0 ([true] : List Bool), (wordSemLastN 0 ([true] : List Bool)).length, decide ((wordSemLastN 0 ([true] : List Bool)).length ≤ 0), decide ((wordSemLastN 0 ([true] : List Bool)).length ≤ 1), (wordSemLastN 0 ([true] : List Bool)).all id) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Bool_1_0
example : (wordSemLastN (0+1) ([true] : List Bool), (wordSemLastN (0+1) ([true] : List Bool)).tail, wordSemLastN 0 ([true] : List Bool), decide (0+1 ≤ 1)) = ([true], [], [], true) := by decide +kernel

-- sl_suffix_Bool_1_1
example : (wordSemLastN 1 ([true] : List Bool), (wordSemLastN 1 ([true] : List Bool)).length, decide ((wordSemLastN 1 ([true] : List Bool)).length ≤ 1), decide ((wordSemLastN 1 ([true] : List Bool)).length ≤ 1), (wordSemLastN 1 ([true] : List Bool)).all id) = ([true], 1, true, true, true) := by decide +kernel

-- sl_less_Bool_1_1
example : (wordSemLastN (1+1) ([true] : List Bool), (wordSemLastN (1+1) ([true] : List Bool)).tail, wordSemLastN 1 ([true] : List Bool), decide (1+1 ≤ 1)) = ([true], [], [true], false) := by decide +kernel

-- sl_suffix_Bool_1_2
example : (wordSemLastN 2 ([true] : List Bool), (wordSemLastN 2 ([true] : List Bool)).length, decide ((wordSemLastN 2 ([true] : List Bool)).length ≤ 2), decide ((wordSemLastN 2 ([true] : List Bool)).length ≤ 1), (wordSemLastN 2 ([true] : List Bool)).all id) = ([true], 1, true, true, true) := by decide +kernel

-- sl_less_Bool_1_2
example : (wordSemLastN (2+1) ([true] : List Bool), (wordSemLastN (2+1) ([true] : List Bool)).tail, wordSemLastN 2 ([true] : List Bool), decide (2+1 ≤ 1)) = ([true], [], [true], false) := by decide +kernel

-- sl_suffix_Bool_1_3
example : (wordSemLastN 3 ([true] : List Bool), (wordSemLastN 3 ([true] : List Bool)).length, decide ((wordSemLastN 3 ([true] : List Bool)).length ≤ 3), decide ((wordSemLastN 3 ([true] : List Bool)).length ≤ 1), (wordSemLastN 3 ([true] : List Bool)).all id) = ([true], 1, true, true, true) := by decide +kernel

-- sl_less_Bool_1_3
example : (wordSemLastN (3+1) ([true] : List Bool), (wordSemLastN (3+1) ([true] : List Bool)).tail, wordSemLastN 3 ([true] : List Bool), decide (3+1 ≤ 1)) = ([true], [], [true], false) := by decide +kernel

-- sl_suffix_Bool_1_99
example : (wordSemLastN 99 ([true] : List Bool), (wordSemLastN 99 ([true] : List Bool)).length, decide ((wordSemLastN 99 ([true] : List Bool)).length ≤ 99), decide ((wordSemLastN 99 ([true] : List Bool)).length ≤ 1), (wordSemLastN 99 ([true] : List Bool)).all id) = ([true], 1, true, true, true) := by decide +kernel

-- sl_less_Bool_1_99
example : (wordSemLastN (99+1) ([true] : List Bool), (wordSemLastN (99+1) ([true] : List Bool)).tail, wordSemLastN 99 ([true] : List Bool), decide (99+1 ≤ 1)) = ([true], [], [true], false) := by decide +kernel

-- sl_suffix_Bool_1_900
example : (wordSemLastN 900 ([true] : List Bool), (wordSemLastN 900 ([true] : List Bool)).length, decide ((wordSemLastN 900 ([true] : List Bool)).length ≤ 900), decide ((wordSemLastN 900 ([true] : List Bool)).length ≤ 1), (wordSemLastN 900 ([true] : List Bool)).all id) = ([true], 1, true, true, true) := by decide +kernel

-- sl_less_Bool_1_900
example : (wordSemLastN (900+1) ([true] : List Bool), (wordSemLastN (900+1) ([true] : List Bool)).tail, wordSemLastN 900 ([true] : List Bool), decide (900+1 ≤ 1)) = ([true], [], [true], false) := by decide +kernel

-- sl_head_Bool_1
example : (wordSemLastN 1 ([true] : List Bool), ([true] : List Bool).head (by simp) :: wordSemLastN 0 ([true] : List Bool)) = ([true], [true]) := by decide +kernel

-- sl_cons_Bool_1_0
example : wordSemLastN (1+1) (false::([true] : List Bool)) = [false, true] := by decide +kernel

-- sl_cons_Bool_1_1
example : wordSemLastN (1+1) (true::([true] : List Bool)) = [true, true] := by decide +kernel

-- sl_suffix_Bool_2_0
example : (wordSemLastN 0 ([false] : List Bool), (wordSemLastN 0 ([false] : List Bool)).length, decide ((wordSemLastN 0 ([false] : List Bool)).length ≤ 0), decide ((wordSemLastN 0 ([false] : List Bool)).length ≤ 1), (wordSemLastN 0 ([false] : List Bool)).all id) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Bool_2_0
example : (wordSemLastN (0+1) ([false] : List Bool), (wordSemLastN (0+1) ([false] : List Bool)).tail, wordSemLastN 0 ([false] : List Bool), decide (0+1 ≤ 1)) = ([false], [], [], true) := by decide +kernel

-- sl_suffix_Bool_2_1
example : (wordSemLastN 1 ([false] : List Bool), (wordSemLastN 1 ([false] : List Bool)).length, decide ((wordSemLastN 1 ([false] : List Bool)).length ≤ 1), decide ((wordSemLastN 1 ([false] : List Bool)).length ≤ 1), (wordSemLastN 1 ([false] : List Bool)).all id) = ([false], 1, true, true, false) := by decide +kernel

-- sl_less_Bool_2_1
example : (wordSemLastN (1+1) ([false] : List Bool), (wordSemLastN (1+1) ([false] : List Bool)).tail, wordSemLastN 1 ([false] : List Bool), decide (1+1 ≤ 1)) = ([false], [], [false], false) := by decide +kernel

-- sl_suffix_Bool_2_2
example : (wordSemLastN 2 ([false] : List Bool), (wordSemLastN 2 ([false] : List Bool)).length, decide ((wordSemLastN 2 ([false] : List Bool)).length ≤ 2), decide ((wordSemLastN 2 ([false] : List Bool)).length ≤ 1), (wordSemLastN 2 ([false] : List Bool)).all id) = ([false], 1, true, true, false) := by decide +kernel

-- sl_less_Bool_2_2
example : (wordSemLastN (2+1) ([false] : List Bool), (wordSemLastN (2+1) ([false] : List Bool)).tail, wordSemLastN 2 ([false] : List Bool), decide (2+1 ≤ 1)) = ([false], [], [false], false) := by decide +kernel

-- sl_suffix_Bool_2_3
example : (wordSemLastN 3 ([false] : List Bool), (wordSemLastN 3 ([false] : List Bool)).length, decide ((wordSemLastN 3 ([false] : List Bool)).length ≤ 3), decide ((wordSemLastN 3 ([false] : List Bool)).length ≤ 1), (wordSemLastN 3 ([false] : List Bool)).all id) = ([false], 1, true, true, false) := by decide +kernel

-- sl_less_Bool_2_3
example : (wordSemLastN (3+1) ([false] : List Bool), (wordSemLastN (3+1) ([false] : List Bool)).tail, wordSemLastN 3 ([false] : List Bool), decide (3+1 ≤ 1)) = ([false], [], [false], false) := by decide +kernel

-- sl_suffix_Bool_2_99
example : (wordSemLastN 99 ([false] : List Bool), (wordSemLastN 99 ([false] : List Bool)).length, decide ((wordSemLastN 99 ([false] : List Bool)).length ≤ 99), decide ((wordSemLastN 99 ([false] : List Bool)).length ≤ 1), (wordSemLastN 99 ([false] : List Bool)).all id) = ([false], 1, true, true, false) := by decide +kernel

-- sl_less_Bool_2_99
example : (wordSemLastN (99+1) ([false] : List Bool), (wordSemLastN (99+1) ([false] : List Bool)).tail, wordSemLastN 99 ([false] : List Bool), decide (99+1 ≤ 1)) = ([false], [], [false], false) := by decide +kernel

-- sl_suffix_Bool_2_900
example : (wordSemLastN 900 ([false] : List Bool), (wordSemLastN 900 ([false] : List Bool)).length, decide ((wordSemLastN 900 ([false] : List Bool)).length ≤ 900), decide ((wordSemLastN 900 ([false] : List Bool)).length ≤ 1), (wordSemLastN 900 ([false] : List Bool)).all id) = ([false], 1, true, true, false) := by decide +kernel

-- sl_less_Bool_2_900
example : (wordSemLastN (900+1) ([false] : List Bool), (wordSemLastN (900+1) ([false] : List Bool)).tail, wordSemLastN 900 ([false] : List Bool), decide (900+1 ≤ 1)) = ([false], [], [false], false) := by decide +kernel

-- sl_head_Bool_2
example : (wordSemLastN 1 ([false] : List Bool), ([false] : List Bool).head (by simp) :: wordSemLastN 0 ([false] : List Bool)) = ([false], [false]) := by decide +kernel

-- sl_cons_Bool_2_0
example : wordSemLastN (1+1) (false::([false] : List Bool)) = [false, false] := by decide +kernel

-- sl_cons_Bool_2_1
example : wordSemLastN (1+1) (true::([false] : List Bool)) = [true, false] := by decide +kernel

-- sl_suffix_Bool_3_0
example : (wordSemLastN 0 ([true, false] : List Bool), (wordSemLastN 0 ([true, false] : List Bool)).length, decide ((wordSemLastN 0 ([true, false] : List Bool)).length ≤ 0), decide ((wordSemLastN 0 ([true, false] : List Bool)).length ≤ 2), (wordSemLastN 0 ([true, false] : List Bool)).all id) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Bool_3_0
example : (wordSemLastN (0+1) ([true, false] : List Bool), (wordSemLastN (0+1) ([true, false] : List Bool)).tail, wordSemLastN 0 ([true, false] : List Bool), decide (0+1 ≤ 2)) = ([false], [], [], true) := by decide +kernel

-- sl_suffix_Bool_3_1
example : (wordSemLastN 1 ([true, false] : List Bool), (wordSemLastN 1 ([true, false] : List Bool)).length, decide ((wordSemLastN 1 ([true, false] : List Bool)).length ≤ 1), decide ((wordSemLastN 1 ([true, false] : List Bool)).length ≤ 2), (wordSemLastN 1 ([true, false] : List Bool)).all id) = ([false], 1, true, true, false) := by decide +kernel

-- sl_less_Bool_3_1
example : (wordSemLastN (1+1) ([true, false] : List Bool), (wordSemLastN (1+1) ([true, false] : List Bool)).tail, wordSemLastN 1 ([true, false] : List Bool), decide (1+1 ≤ 2)) = ([true, false], [false], [false], true) := by decide +kernel

-- sl_suffix_Bool_3_2
example : (wordSemLastN 2 ([true, false] : List Bool), (wordSemLastN 2 ([true, false] : List Bool)).length, decide ((wordSemLastN 2 ([true, false] : List Bool)).length ≤ 2), decide ((wordSemLastN 2 ([true, false] : List Bool)).length ≤ 2), (wordSemLastN 2 ([true, false] : List Bool)).all id) = ([true, false], 2, true, true, false) := by decide +kernel

-- sl_less_Bool_3_2
example : (wordSemLastN (2+1) ([true, false] : List Bool), (wordSemLastN (2+1) ([true, false] : List Bool)).tail, wordSemLastN 2 ([true, false] : List Bool), decide (2+1 ≤ 2)) = ([true, false], [false], [true, false], false) := by decide +kernel

-- sl_suffix_Bool_3_3
example : (wordSemLastN 3 ([true, false] : List Bool), (wordSemLastN 3 ([true, false] : List Bool)).length, decide ((wordSemLastN 3 ([true, false] : List Bool)).length ≤ 3), decide ((wordSemLastN 3 ([true, false] : List Bool)).length ≤ 2), (wordSemLastN 3 ([true, false] : List Bool)).all id) = ([true, false], 2, true, true, false) := by decide +kernel

-- sl_less_Bool_3_3
example : (wordSemLastN (3+1) ([true, false] : List Bool), (wordSemLastN (3+1) ([true, false] : List Bool)).tail, wordSemLastN 3 ([true, false] : List Bool), decide (3+1 ≤ 2)) = ([true, false], [false], [true, false], false) := by decide +kernel

-- sl_suffix_Bool_3_4
example : (wordSemLastN 4 ([true, false] : List Bool), (wordSemLastN 4 ([true, false] : List Bool)).length, decide ((wordSemLastN 4 ([true, false] : List Bool)).length ≤ 4), decide ((wordSemLastN 4 ([true, false] : List Bool)).length ≤ 2), (wordSemLastN 4 ([true, false] : List Bool)).all id) = ([true, false], 2, true, true, false) := by decide +kernel

-- sl_less_Bool_3_4
example : (wordSemLastN (4+1) ([true, false] : List Bool), (wordSemLastN (4+1) ([true, false] : List Bool)).tail, wordSemLastN 4 ([true, false] : List Bool), decide (4+1 ≤ 2)) = ([true, false], [false], [true, false], false) := by decide +kernel

-- sl_suffix_Bool_3_99
example : (wordSemLastN 99 ([true, false] : List Bool), (wordSemLastN 99 ([true, false] : List Bool)).length, decide ((wordSemLastN 99 ([true, false] : List Bool)).length ≤ 99), decide ((wordSemLastN 99 ([true, false] : List Bool)).length ≤ 2), (wordSemLastN 99 ([true, false] : List Bool)).all id) = ([true, false], 2, true, true, false) := by decide +kernel

-- sl_less_Bool_3_99
example : (wordSemLastN (99+1) ([true, false] : List Bool), (wordSemLastN (99+1) ([true, false] : List Bool)).tail, wordSemLastN 99 ([true, false] : List Bool), decide (99+1 ≤ 2)) = ([true, false], [false], [true, false], false) := by decide +kernel

-- sl_suffix_Bool_3_900
example : (wordSemLastN 900 ([true, false] : List Bool), (wordSemLastN 900 ([true, false] : List Bool)).length, decide ((wordSemLastN 900 ([true, false] : List Bool)).length ≤ 900), decide ((wordSemLastN 900 ([true, false] : List Bool)).length ≤ 2), (wordSemLastN 900 ([true, false] : List Bool)).all id) = ([true, false], 2, true, true, false) := by decide +kernel

-- sl_less_Bool_3_900
example : (wordSemLastN (900+1) ([true, false] : List Bool), (wordSemLastN (900+1) ([true, false] : List Bool)).tail, wordSemLastN 900 ([true, false] : List Bool), decide (900+1 ≤ 2)) = ([true, false], [false], [true, false], false) := by decide +kernel

-- sl_head_Bool_3
example : (wordSemLastN 2 ([true, false] : List Bool), ([true, false] : List Bool).head (by simp) :: wordSemLastN 1 ([true, false] : List Bool)) = ([true, false], [true, false]) := by decide +kernel

-- sl_cons_Bool_3_0
example : wordSemLastN (2+1) (false::([true, false] : List Bool)) = [false, true, false] := by decide +kernel

-- sl_cons_Bool_3_1
example : wordSemLastN (2+1) (true::([true, false] : List Bool)) = [true, true, false] := by decide +kernel

-- sl_suffix_Bool_4_0
example : (wordSemLastN 0 ([false, true, false] : List Bool), (wordSemLastN 0 ([false, true, false] : List Bool)).length, decide ((wordSemLastN 0 ([false, true, false] : List Bool)).length ≤ 0), decide ((wordSemLastN 0 ([false, true, false] : List Bool)).length ≤ 3), (wordSemLastN 0 ([false, true, false] : List Bool)).all id) = ([], 0, true, true, true) := by decide +kernel

-- sl_less_Bool_4_0
example : (wordSemLastN (0+1) ([false, true, false] : List Bool), (wordSemLastN (0+1) ([false, true, false] : List Bool)).tail, wordSemLastN 0 ([false, true, false] : List Bool), decide (0+1 ≤ 3)) = ([false], [], [], true) := by decide +kernel

-- sl_suffix_Bool_4_1
example : (wordSemLastN 1 ([false, true, false] : List Bool), (wordSemLastN 1 ([false, true, false] : List Bool)).length, decide ((wordSemLastN 1 ([false, true, false] : List Bool)).length ≤ 1), decide ((wordSemLastN 1 ([false, true, false] : List Bool)).length ≤ 3), (wordSemLastN 1 ([false, true, false] : List Bool)).all id) = ([false], 1, true, true, false) := by decide +kernel

-- sl_less_Bool_4_1
example : (wordSemLastN (1+1) ([false, true, false] : List Bool), (wordSemLastN (1+1) ([false, true, false] : List Bool)).tail, wordSemLastN 1 ([false, true, false] : List Bool), decide (1+1 ≤ 3)) = ([true, false], [false], [false], true) := by decide +kernel

-- sl_suffix_Bool_4_2
example : (wordSemLastN 2 ([false, true, false] : List Bool), (wordSemLastN 2 ([false, true, false] : List Bool)).length, decide ((wordSemLastN 2 ([false, true, false] : List Bool)).length ≤ 2), decide ((wordSemLastN 2 ([false, true, false] : List Bool)).length ≤ 3), (wordSemLastN 2 ([false, true, false] : List Bool)).all id) = ([true, false], 2, true, true, false) := by decide +kernel

-- sl_less_Bool_4_2
example : (wordSemLastN (2+1) ([false, true, false] : List Bool), (wordSemLastN (2+1) ([false, true, false] : List Bool)).tail, wordSemLastN 2 ([false, true, false] : List Bool), decide (2+1 ≤ 3)) = ([false, true, false], [true, false], [true, false], true) := by decide +kernel

-- sl_suffix_Bool_4_3
example : (wordSemLastN 3 ([false, true, false] : List Bool), (wordSemLastN 3 ([false, true, false] : List Bool)).length, decide ((wordSemLastN 3 ([false, true, false] : List Bool)).length ≤ 3), decide ((wordSemLastN 3 ([false, true, false] : List Bool)).length ≤ 3), (wordSemLastN 3 ([false, true, false] : List Bool)).all id) = ([false, true, false], 3, true, true, false) := by decide +kernel

-- sl_less_Bool_4_3
example : (wordSemLastN (3+1) ([false, true, false] : List Bool), (wordSemLastN (3+1) ([false, true, false] : List Bool)).tail, wordSemLastN 3 ([false, true, false] : List Bool), decide (3+1 ≤ 3)) = ([false, true, false], [true, false], [false, true, false], false) := by decide +kernel

-- sl_suffix_Bool_4_4
example : (wordSemLastN 4 ([false, true, false] : List Bool), (wordSemLastN 4 ([false, true, false] : List Bool)).length, decide ((wordSemLastN 4 ([false, true, false] : List Bool)).length ≤ 4), decide ((wordSemLastN 4 ([false, true, false] : List Bool)).length ≤ 3), (wordSemLastN 4 ([false, true, false] : List Bool)).all id) = ([false, true, false], 3, true, true, false) := by decide +kernel

-- sl_less_Bool_4_4
example : (wordSemLastN (4+1) ([false, true, false] : List Bool), (wordSemLastN (4+1) ([false, true, false] : List Bool)).tail, wordSemLastN 4 ([false, true, false] : List Bool), decide (4+1 ≤ 3)) = ([false, true, false], [true, false], [false, true, false], false) := by decide +kernel

-- sl_suffix_Bool_4_5
example : (wordSemLastN 5 ([false, true, false] : List Bool), (wordSemLastN 5 ([false, true, false] : List Bool)).length, decide ((wordSemLastN 5 ([false, true, false] : List Bool)).length ≤ 5), decide ((wordSemLastN 5 ([false, true, false] : List Bool)).length ≤ 3), (wordSemLastN 5 ([false, true, false] : List Bool)).all id) = ([false, true, false], 3, true, true, false) := by decide +kernel

-- sl_less_Bool_4_5
example : (wordSemLastN (5+1) ([false, true, false] : List Bool), (wordSemLastN (5+1) ([false, true, false] : List Bool)).tail, wordSemLastN 5 ([false, true, false] : List Bool), decide (5+1 ≤ 3)) = ([false, true, false], [true, false], [false, true, false], false) := by decide +kernel

-- sl_suffix_Bool_4_99
example : (wordSemLastN 99 ([false, true, false] : List Bool), (wordSemLastN 99 ([false, true, false] : List Bool)).length, decide ((wordSemLastN 99 ([false, true, false] : List Bool)).length ≤ 99), decide ((wordSemLastN 99 ([false, true, false] : List Bool)).length ≤ 3), (wordSemLastN 99 ([false, true, false] : List Bool)).all id) = ([false, true, false], 3, true, true, false) := by decide +kernel

-- sl_less_Bool_4_99
example : (wordSemLastN (99+1) ([false, true, false] : List Bool), (wordSemLastN (99+1) ([false, true, false] : List Bool)).tail, wordSemLastN 99 ([false, true, false] : List Bool), decide (99+1 ≤ 3)) = ([false, true, false], [true, false], [false, true, false], false) := by decide +kernel

-- sl_suffix_Bool_4_900
example : (wordSemLastN 900 ([false, true, false] : List Bool), (wordSemLastN 900 ([false, true, false] : List Bool)).length, decide ((wordSemLastN 900 ([false, true, false] : List Bool)).length ≤ 900), decide ((wordSemLastN 900 ([false, true, false] : List Bool)).length ≤ 3), (wordSemLastN 900 ([false, true, false] : List Bool)).all id) = ([false, true, false], 3, true, true, false) := by decide +kernel

-- sl_less_Bool_4_900
example : (wordSemLastN (900+1) ([false, true, false] : List Bool), (wordSemLastN (900+1) ([false, true, false] : List Bool)).tail, wordSemLastN 900 ([false, true, false] : List Bool), decide (900+1 ≤ 3)) = ([false, true, false], [true, false], [false, true, false], false) := by decide +kernel

-- sl_head_Bool_4
example : (wordSemLastN 3 ([false, true, false] : List Bool), ([false, true, false] : List Bool).head (by simp) :: wordSemLastN 2 ([false, true, false] : List Bool)) = ([false, true, false], [false, true, false]) := by decide +kernel

-- sl_cons_Bool_4_0
example : wordSemLastN (3+1) (false::([false, true, false] : List Bool)) = [false, false, true, false] := by decide +kernel

-- sl_cons_Bool_4_1
example : wordSemLastN (3+1) (true::([false, true, false] : List Bool)) = [true, false, true, false] := by decide +kernel

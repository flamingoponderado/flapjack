import Flapjack.Compiler.Backend.WordToStack.Proofs.LiveListSupport
open Flapjack.Compiler.Backend.WordToStack

-- ll_prefix_0_0_0
example : ([] : List Nat).IsPrefix ([] : List Nat) → (([] : List Nat).drop 0).IsPrefix (([] : List Nat).drop 0) := by decide

-- ll_prefix_0_0_1
example : ([] : List Nat).IsPrefix ([] : List Nat) → (([] : List Nat).drop 1).IsPrefix (([] : List Nat).drop 1) := by decide

-- ll_prefix_0_0_3
example : ([] : List Nat).IsPrefix ([] : List Nat) → (([] : List Nat).drop 3).IsPrefix (([] : List Nat).drop 3) := by decide

-- ll_prefix_0_0_9
example : ([] : List Nat).IsPrefix ([] : List Nat) → (([] : List Nat).drop 9).IsPrefix (([] : List Nat).drop 9) := by decide

-- ll_prefix_0_1_0
example : ([] : List Nat).IsPrefix ([0] : List Nat) → (([] : List Nat).drop 0).IsPrefix (([0] : List Nat).drop 0) := by decide

-- ll_prefix_0_1_1
example : ([] : List Nat).IsPrefix ([0] : List Nat) → (([] : List Nat).drop 1).IsPrefix (([0] : List Nat).drop 1) := by decide

-- ll_prefix_0_1_3
example : ([] : List Nat).IsPrefix ([0] : List Nat) → (([] : List Nat).drop 3).IsPrefix (([0] : List Nat).drop 3) := by decide

-- ll_prefix_0_1_9
example : ([] : List Nat).IsPrefix ([0] : List Nat) → (([] : List Nat).drop 9).IsPrefix (([0] : List Nat).drop 9) := by decide

-- ll_prefix_0_2_0
example : ([] : List Nat).IsPrefix ([0, 1] : List Nat) → (([] : List Nat).drop 0).IsPrefix (([0, 1] : List Nat).drop 0) := by decide

-- ll_prefix_0_2_1
example : ([] : List Nat).IsPrefix ([0, 1] : List Nat) → (([] : List Nat).drop 1).IsPrefix (([0, 1] : List Nat).drop 1) := by decide

-- ll_prefix_0_2_3
example : ([] : List Nat).IsPrefix ([0, 1] : List Nat) → (([] : List Nat).drop 3).IsPrefix (([0, 1] : List Nat).drop 3) := by decide

-- ll_prefix_0_2_9
example : ([] : List Nat).IsPrefix ([0, 1] : List Nat) → (([] : List Nat).drop 9).IsPrefix (([0, 1] : List Nat).drop 9) := by decide

-- ll_prefix_0_3_0
example : ([] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([] : List Nat).drop 0).IsPrefix (([0, 1, 2] : List Nat).drop 0) := by decide

-- ll_prefix_0_3_1
example : ([] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([] : List Nat).drop 1).IsPrefix (([0, 1, 2] : List Nat).drop 1) := by decide

-- ll_prefix_0_3_3
example : ([] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([] : List Nat).drop 3).IsPrefix (([0, 1, 2] : List Nat).drop 3) := by decide

-- ll_prefix_0_3_9
example : ([] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([] : List Nat).drop 9).IsPrefix (([0, 1, 2] : List Nat).drop 9) := by decide

-- ll_prefix_0_4_0
example : ([] : List Nat).IsPrefix ([2, 0] : List Nat) → (([] : List Nat).drop 0).IsPrefix (([2, 0] : List Nat).drop 0) := by decide

-- ll_prefix_0_4_1
example : ([] : List Nat).IsPrefix ([2, 0] : List Nat) → (([] : List Nat).drop 1).IsPrefix (([2, 0] : List Nat).drop 1) := by decide

-- ll_prefix_0_4_3
example : ([] : List Nat).IsPrefix ([2, 0] : List Nat) → (([] : List Nat).drop 3).IsPrefix (([2, 0] : List Nat).drop 3) := by decide

-- ll_prefix_0_4_9
example : ([] : List Nat).IsPrefix ([2, 0] : List Nat) → (([] : List Nat).drop 9).IsPrefix (([2, 0] : List Nat).drop 9) := by decide

-- ll_prefix_0_5_0
example : ([] : List Nat).IsPrefix ([0, 0] : List Nat) → (([] : List Nat).drop 0).IsPrefix (([0, 0] : List Nat).drop 0) := by decide

-- ll_prefix_0_5_1
example : ([] : List Nat).IsPrefix ([0, 0] : List Nat) → (([] : List Nat).drop 1).IsPrefix (([0, 0] : List Nat).drop 1) := by decide

-- ll_prefix_0_5_3
example : ([] : List Nat).IsPrefix ([0, 0] : List Nat) → (([] : List Nat).drop 3).IsPrefix (([0, 0] : List Nat).drop 3) := by decide

-- ll_prefix_0_5_9
example : ([] : List Nat).IsPrefix ([0, 0] : List Nat) → (([] : List Nat).drop 9).IsPrefix (([0, 0] : List Nat).drop 9) := by decide

-- ll_prefix_1_0_0
example : ([0] : List Nat).IsPrefix ([] : List Nat) → (([0] : List Nat).drop 0).IsPrefix (([] : List Nat).drop 0) := by decide

-- ll_prefix_1_0_1
example : ([0] : List Nat).IsPrefix ([] : List Nat) → (([0] : List Nat).drop 1).IsPrefix (([] : List Nat).drop 1) := by decide

-- ll_prefix_1_0_3
example : ([0] : List Nat).IsPrefix ([] : List Nat) → (([0] : List Nat).drop 3).IsPrefix (([] : List Nat).drop 3) := by decide

-- ll_prefix_1_0_9
example : ([0] : List Nat).IsPrefix ([] : List Nat) → (([0] : List Nat).drop 9).IsPrefix (([] : List Nat).drop 9) := by decide

-- ll_prefix_1_1_0
example : ([0] : List Nat).IsPrefix ([0] : List Nat) → (([0] : List Nat).drop 0).IsPrefix (([0] : List Nat).drop 0) := by decide

-- ll_prefix_1_1_1
example : ([0] : List Nat).IsPrefix ([0] : List Nat) → (([0] : List Nat).drop 1).IsPrefix (([0] : List Nat).drop 1) := by decide

-- ll_prefix_1_1_3
example : ([0] : List Nat).IsPrefix ([0] : List Nat) → (([0] : List Nat).drop 3).IsPrefix (([0] : List Nat).drop 3) := by decide

-- ll_prefix_1_1_9
example : ([0] : List Nat).IsPrefix ([0] : List Nat) → (([0] : List Nat).drop 9).IsPrefix (([0] : List Nat).drop 9) := by decide

-- ll_prefix_1_2_0
example : ([0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0] : List Nat).drop 0).IsPrefix (([0, 1] : List Nat).drop 0) := by decide

-- ll_prefix_1_2_1
example : ([0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0] : List Nat).drop 1).IsPrefix (([0, 1] : List Nat).drop 1) := by decide

-- ll_prefix_1_2_3
example : ([0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0] : List Nat).drop 3).IsPrefix (([0, 1] : List Nat).drop 3) := by decide

-- ll_prefix_1_2_9
example : ([0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0] : List Nat).drop 9).IsPrefix (([0, 1] : List Nat).drop 9) := by decide

-- ll_prefix_1_3_0
example : ([0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0] : List Nat).drop 0).IsPrefix (([0, 1, 2] : List Nat).drop 0) := by decide

-- ll_prefix_1_3_1
example : ([0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0] : List Nat).drop 1).IsPrefix (([0, 1, 2] : List Nat).drop 1) := by decide

-- ll_prefix_1_3_3
example : ([0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0] : List Nat).drop 3).IsPrefix (([0, 1, 2] : List Nat).drop 3) := by decide

-- ll_prefix_1_3_9
example : ([0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0] : List Nat).drop 9).IsPrefix (([0, 1, 2] : List Nat).drop 9) := by decide

-- ll_prefix_1_4_0
example : ([0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0] : List Nat).drop 0).IsPrefix (([2, 0] : List Nat).drop 0) := by decide

-- ll_prefix_1_4_1
example : ([0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0] : List Nat).drop 1).IsPrefix (([2, 0] : List Nat).drop 1) := by decide

-- ll_prefix_1_4_3
example : ([0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0] : List Nat).drop 3).IsPrefix (([2, 0] : List Nat).drop 3) := by decide

-- ll_prefix_1_4_9
example : ([0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0] : List Nat).drop 9).IsPrefix (([2, 0] : List Nat).drop 9) := by decide

-- ll_prefix_1_5_0
example : ([0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0] : List Nat).drop 0).IsPrefix (([0, 0] : List Nat).drop 0) := by decide

-- ll_prefix_1_5_1
example : ([0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0] : List Nat).drop 1).IsPrefix (([0, 0] : List Nat).drop 1) := by decide

-- ll_prefix_1_5_3
example : ([0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0] : List Nat).drop 3).IsPrefix (([0, 0] : List Nat).drop 3) := by decide

-- ll_prefix_1_5_9
example : ([0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0] : List Nat).drop 9).IsPrefix (([0, 0] : List Nat).drop 9) := by decide

-- ll_prefix_2_0_0
example : ([0, 1] : List Nat).IsPrefix ([] : List Nat) → (([0, 1] : List Nat).drop 0).IsPrefix (([] : List Nat).drop 0) := by decide

-- ll_prefix_2_0_1
example : ([0, 1] : List Nat).IsPrefix ([] : List Nat) → (([0, 1] : List Nat).drop 1).IsPrefix (([] : List Nat).drop 1) := by decide

-- ll_prefix_2_0_3
example : ([0, 1] : List Nat).IsPrefix ([] : List Nat) → (([0, 1] : List Nat).drop 3).IsPrefix (([] : List Nat).drop 3) := by decide

-- ll_prefix_2_0_9
example : ([0, 1] : List Nat).IsPrefix ([] : List Nat) → (([0, 1] : List Nat).drop 9).IsPrefix (([] : List Nat).drop 9) := by decide

-- ll_prefix_2_1_0
example : ([0, 1] : List Nat).IsPrefix ([0] : List Nat) → (([0, 1] : List Nat).drop 0).IsPrefix (([0] : List Nat).drop 0) := by decide

-- ll_prefix_2_1_1
example : ([0, 1] : List Nat).IsPrefix ([0] : List Nat) → (([0, 1] : List Nat).drop 1).IsPrefix (([0] : List Nat).drop 1) := by decide

-- ll_prefix_2_1_3
example : ([0, 1] : List Nat).IsPrefix ([0] : List Nat) → (([0, 1] : List Nat).drop 3).IsPrefix (([0] : List Nat).drop 3) := by decide

-- ll_prefix_2_1_9
example : ([0, 1] : List Nat).IsPrefix ([0] : List Nat) → (([0, 1] : List Nat).drop 9).IsPrefix (([0] : List Nat).drop 9) := by decide

-- ll_prefix_2_2_0
example : ([0, 1] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 1] : List Nat).drop 0).IsPrefix (([0, 1] : List Nat).drop 0) := by decide

-- ll_prefix_2_2_1
example : ([0, 1] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 1] : List Nat).drop 1).IsPrefix (([0, 1] : List Nat).drop 1) := by decide

-- ll_prefix_2_2_3
example : ([0, 1] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 1] : List Nat).drop 3).IsPrefix (([0, 1] : List Nat).drop 3) := by decide

-- ll_prefix_2_2_9
example : ([0, 1] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 1] : List Nat).drop 9).IsPrefix (([0, 1] : List Nat).drop 9) := by decide

-- ll_prefix_2_3_0
example : ([0, 1] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 1] : List Nat).drop 0).IsPrefix (([0, 1, 2] : List Nat).drop 0) := by decide

-- ll_prefix_2_3_1
example : ([0, 1] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 1] : List Nat).drop 1).IsPrefix (([0, 1, 2] : List Nat).drop 1) := by decide

-- ll_prefix_2_3_3
example : ([0, 1] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 1] : List Nat).drop 3).IsPrefix (([0, 1, 2] : List Nat).drop 3) := by decide

-- ll_prefix_2_3_9
example : ([0, 1] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 1] : List Nat).drop 9).IsPrefix (([0, 1, 2] : List Nat).drop 9) := by decide

-- ll_prefix_2_4_0
example : ([0, 1] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 1] : List Nat).drop 0).IsPrefix (([2, 0] : List Nat).drop 0) := by decide

-- ll_prefix_2_4_1
example : ([0, 1] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 1] : List Nat).drop 1).IsPrefix (([2, 0] : List Nat).drop 1) := by decide

-- ll_prefix_2_4_3
example : ([0, 1] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 1] : List Nat).drop 3).IsPrefix (([2, 0] : List Nat).drop 3) := by decide

-- ll_prefix_2_4_9
example : ([0, 1] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 1] : List Nat).drop 9).IsPrefix (([2, 0] : List Nat).drop 9) := by decide

-- ll_prefix_2_5_0
example : ([0, 1] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 1] : List Nat).drop 0).IsPrefix (([0, 0] : List Nat).drop 0) := by decide

-- ll_prefix_2_5_1
example : ([0, 1] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 1] : List Nat).drop 1).IsPrefix (([0, 0] : List Nat).drop 1) := by decide

-- ll_prefix_2_5_3
example : ([0, 1] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 1] : List Nat).drop 3).IsPrefix (([0, 0] : List Nat).drop 3) := by decide

-- ll_prefix_2_5_9
example : ([0, 1] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 1] : List Nat).drop 9).IsPrefix (([0, 0] : List Nat).drop 9) := by decide

-- ll_prefix_3_0_0
example : ([0, 1, 2] : List Nat).IsPrefix ([] : List Nat) → (([0, 1, 2] : List Nat).drop 0).IsPrefix (([] : List Nat).drop 0) := by decide

-- ll_prefix_3_0_1
example : ([0, 1, 2] : List Nat).IsPrefix ([] : List Nat) → (([0, 1, 2] : List Nat).drop 1).IsPrefix (([] : List Nat).drop 1) := by decide

-- ll_prefix_3_0_3
example : ([0, 1, 2] : List Nat).IsPrefix ([] : List Nat) → (([0, 1, 2] : List Nat).drop 3).IsPrefix (([] : List Nat).drop 3) := by decide

-- ll_prefix_3_0_9
example : ([0, 1, 2] : List Nat).IsPrefix ([] : List Nat) → (([0, 1, 2] : List Nat).drop 9).IsPrefix (([] : List Nat).drop 9) := by decide

-- ll_prefix_3_1_0
example : ([0, 1, 2] : List Nat).IsPrefix ([0] : List Nat) → (([0, 1, 2] : List Nat).drop 0).IsPrefix (([0] : List Nat).drop 0) := by decide

-- ll_prefix_3_1_1
example : ([0, 1, 2] : List Nat).IsPrefix ([0] : List Nat) → (([0, 1, 2] : List Nat).drop 1).IsPrefix (([0] : List Nat).drop 1) := by decide

-- ll_prefix_3_1_3
example : ([0, 1, 2] : List Nat).IsPrefix ([0] : List Nat) → (([0, 1, 2] : List Nat).drop 3).IsPrefix (([0] : List Nat).drop 3) := by decide

-- ll_prefix_3_1_9
example : ([0, 1, 2] : List Nat).IsPrefix ([0] : List Nat) → (([0, 1, 2] : List Nat).drop 9).IsPrefix (([0] : List Nat).drop 9) := by decide

-- ll_prefix_3_2_0
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 1, 2] : List Nat).drop 0).IsPrefix (([0, 1] : List Nat).drop 0) := by decide

-- ll_prefix_3_2_1
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 1, 2] : List Nat).drop 1).IsPrefix (([0, 1] : List Nat).drop 1) := by decide

-- ll_prefix_3_2_3
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 1, 2] : List Nat).drop 3).IsPrefix (([0, 1] : List Nat).drop 3) := by decide

-- ll_prefix_3_2_9
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 1, 2] : List Nat).drop 9).IsPrefix (([0, 1] : List Nat).drop 9) := by decide

-- ll_prefix_3_3_0
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 1, 2] : List Nat).drop 0).IsPrefix (([0, 1, 2] : List Nat).drop 0) := by decide

-- ll_prefix_3_3_1
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 1, 2] : List Nat).drop 1).IsPrefix (([0, 1, 2] : List Nat).drop 1) := by decide

-- ll_prefix_3_3_3
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 1, 2] : List Nat).drop 3).IsPrefix (([0, 1, 2] : List Nat).drop 3) := by decide

-- ll_prefix_3_3_9
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 1, 2] : List Nat).drop 9).IsPrefix (([0, 1, 2] : List Nat).drop 9) := by decide

-- ll_prefix_3_4_0
example : ([0, 1, 2] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 1, 2] : List Nat).drop 0).IsPrefix (([2, 0] : List Nat).drop 0) := by decide

-- ll_prefix_3_4_1
example : ([0, 1, 2] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 1, 2] : List Nat).drop 1).IsPrefix (([2, 0] : List Nat).drop 1) := by decide

-- ll_prefix_3_4_3
example : ([0, 1, 2] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 1, 2] : List Nat).drop 3).IsPrefix (([2, 0] : List Nat).drop 3) := by decide

-- ll_prefix_3_4_9
example : ([0, 1, 2] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 1, 2] : List Nat).drop 9).IsPrefix (([2, 0] : List Nat).drop 9) := by decide

-- ll_prefix_3_5_0
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 1, 2] : List Nat).drop 0).IsPrefix (([0, 0] : List Nat).drop 0) := by decide

-- ll_prefix_3_5_1
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 1, 2] : List Nat).drop 1).IsPrefix (([0, 0] : List Nat).drop 1) := by decide

-- ll_prefix_3_5_3
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 1, 2] : List Nat).drop 3).IsPrefix (([0, 0] : List Nat).drop 3) := by decide

-- ll_prefix_3_5_9
example : ([0, 1, 2] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 1, 2] : List Nat).drop 9).IsPrefix (([0, 0] : List Nat).drop 9) := by decide

-- ll_prefix_4_0_0
example : ([2, 0] : List Nat).IsPrefix ([] : List Nat) → (([2, 0] : List Nat).drop 0).IsPrefix (([] : List Nat).drop 0) := by decide

-- ll_prefix_4_0_1
example : ([2, 0] : List Nat).IsPrefix ([] : List Nat) → (([2, 0] : List Nat).drop 1).IsPrefix (([] : List Nat).drop 1) := by decide

-- ll_prefix_4_0_3
example : ([2, 0] : List Nat).IsPrefix ([] : List Nat) → (([2, 0] : List Nat).drop 3).IsPrefix (([] : List Nat).drop 3) := by decide

-- ll_prefix_4_0_9
example : ([2, 0] : List Nat).IsPrefix ([] : List Nat) → (([2, 0] : List Nat).drop 9).IsPrefix (([] : List Nat).drop 9) := by decide

-- ll_prefix_4_1_0
example : ([2, 0] : List Nat).IsPrefix ([0] : List Nat) → (([2, 0] : List Nat).drop 0).IsPrefix (([0] : List Nat).drop 0) := by decide

-- ll_prefix_4_1_1
example : ([2, 0] : List Nat).IsPrefix ([0] : List Nat) → (([2, 0] : List Nat).drop 1).IsPrefix (([0] : List Nat).drop 1) := by decide

-- ll_prefix_4_1_3
example : ([2, 0] : List Nat).IsPrefix ([0] : List Nat) → (([2, 0] : List Nat).drop 3).IsPrefix (([0] : List Nat).drop 3) := by decide

-- ll_prefix_4_1_9
example : ([2, 0] : List Nat).IsPrefix ([0] : List Nat) → (([2, 0] : List Nat).drop 9).IsPrefix (([0] : List Nat).drop 9) := by decide

-- ll_prefix_4_2_0
example : ([2, 0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([2, 0] : List Nat).drop 0).IsPrefix (([0, 1] : List Nat).drop 0) := by decide

-- ll_prefix_4_2_1
example : ([2, 0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([2, 0] : List Nat).drop 1).IsPrefix (([0, 1] : List Nat).drop 1) := by decide

-- ll_prefix_4_2_3
example : ([2, 0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([2, 0] : List Nat).drop 3).IsPrefix (([0, 1] : List Nat).drop 3) := by decide

-- ll_prefix_4_2_9
example : ([2, 0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([2, 0] : List Nat).drop 9).IsPrefix (([0, 1] : List Nat).drop 9) := by decide

-- ll_prefix_4_3_0
example : ([2, 0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([2, 0] : List Nat).drop 0).IsPrefix (([0, 1, 2] : List Nat).drop 0) := by decide

-- ll_prefix_4_3_1
example : ([2, 0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([2, 0] : List Nat).drop 1).IsPrefix (([0, 1, 2] : List Nat).drop 1) := by decide

-- ll_prefix_4_3_3
example : ([2, 0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([2, 0] : List Nat).drop 3).IsPrefix (([0, 1, 2] : List Nat).drop 3) := by decide

-- ll_prefix_4_3_9
example : ([2, 0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([2, 0] : List Nat).drop 9).IsPrefix (([0, 1, 2] : List Nat).drop 9) := by decide

-- ll_prefix_4_4_0
example : ([2, 0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([2, 0] : List Nat).drop 0).IsPrefix (([2, 0] : List Nat).drop 0) := by decide

-- ll_prefix_4_4_1
example : ([2, 0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([2, 0] : List Nat).drop 1).IsPrefix (([2, 0] : List Nat).drop 1) := by decide

-- ll_prefix_4_4_3
example : ([2, 0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([2, 0] : List Nat).drop 3).IsPrefix (([2, 0] : List Nat).drop 3) := by decide

-- ll_prefix_4_4_9
example : ([2, 0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([2, 0] : List Nat).drop 9).IsPrefix (([2, 0] : List Nat).drop 9) := by decide

-- ll_prefix_4_5_0
example : ([2, 0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([2, 0] : List Nat).drop 0).IsPrefix (([0, 0] : List Nat).drop 0) := by decide

-- ll_prefix_4_5_1
example : ([2, 0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([2, 0] : List Nat).drop 1).IsPrefix (([0, 0] : List Nat).drop 1) := by decide

-- ll_prefix_4_5_3
example : ([2, 0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([2, 0] : List Nat).drop 3).IsPrefix (([0, 0] : List Nat).drop 3) := by decide

-- ll_prefix_4_5_9
example : ([2, 0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([2, 0] : List Nat).drop 9).IsPrefix (([0, 0] : List Nat).drop 9) := by decide

-- ll_prefix_5_0_0
example : ([0, 0] : List Nat).IsPrefix ([] : List Nat) → (([0, 0] : List Nat).drop 0).IsPrefix (([] : List Nat).drop 0) := by decide

-- ll_prefix_5_0_1
example : ([0, 0] : List Nat).IsPrefix ([] : List Nat) → (([0, 0] : List Nat).drop 1).IsPrefix (([] : List Nat).drop 1) := by decide

-- ll_prefix_5_0_3
example : ([0, 0] : List Nat).IsPrefix ([] : List Nat) → (([0, 0] : List Nat).drop 3).IsPrefix (([] : List Nat).drop 3) := by decide

-- ll_prefix_5_0_9
example : ([0, 0] : List Nat).IsPrefix ([] : List Nat) → (([0, 0] : List Nat).drop 9).IsPrefix (([] : List Nat).drop 9) := by decide

-- ll_prefix_5_1_0
example : ([0, 0] : List Nat).IsPrefix ([0] : List Nat) → (([0, 0] : List Nat).drop 0).IsPrefix (([0] : List Nat).drop 0) := by decide

-- ll_prefix_5_1_1
example : ([0, 0] : List Nat).IsPrefix ([0] : List Nat) → (([0, 0] : List Nat).drop 1).IsPrefix (([0] : List Nat).drop 1) := by decide

-- ll_prefix_5_1_3
example : ([0, 0] : List Nat).IsPrefix ([0] : List Nat) → (([0, 0] : List Nat).drop 3).IsPrefix (([0] : List Nat).drop 3) := by decide

-- ll_prefix_5_1_9
example : ([0, 0] : List Nat).IsPrefix ([0] : List Nat) → (([0, 0] : List Nat).drop 9).IsPrefix (([0] : List Nat).drop 9) := by decide

-- ll_prefix_5_2_0
example : ([0, 0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 0] : List Nat).drop 0).IsPrefix (([0, 1] : List Nat).drop 0) := by decide

-- ll_prefix_5_2_1
example : ([0, 0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 0] : List Nat).drop 1).IsPrefix (([0, 1] : List Nat).drop 1) := by decide

-- ll_prefix_5_2_3
example : ([0, 0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 0] : List Nat).drop 3).IsPrefix (([0, 1] : List Nat).drop 3) := by decide

-- ll_prefix_5_2_9
example : ([0, 0] : List Nat).IsPrefix ([0, 1] : List Nat) → (([0, 0] : List Nat).drop 9).IsPrefix (([0, 1] : List Nat).drop 9) := by decide

-- ll_prefix_5_3_0
example : ([0, 0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 0] : List Nat).drop 0).IsPrefix (([0, 1, 2] : List Nat).drop 0) := by decide

-- ll_prefix_5_3_1
example : ([0, 0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 0] : List Nat).drop 1).IsPrefix (([0, 1, 2] : List Nat).drop 1) := by decide

-- ll_prefix_5_3_3
example : ([0, 0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 0] : List Nat).drop 3).IsPrefix (([0, 1, 2] : List Nat).drop 3) := by decide

-- ll_prefix_5_3_9
example : ([0, 0] : List Nat).IsPrefix ([0, 1, 2] : List Nat) → (([0, 0] : List Nat).drop 9).IsPrefix (([0, 1, 2] : List Nat).drop 9) := by decide

-- ll_prefix_5_4_0
example : ([0, 0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 0] : List Nat).drop 0).IsPrefix (([2, 0] : List Nat).drop 0) := by decide

-- ll_prefix_5_4_1
example : ([0, 0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 0] : List Nat).drop 1).IsPrefix (([2, 0] : List Nat).drop 1) := by decide

-- ll_prefix_5_4_3
example : ([0, 0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 0] : List Nat).drop 3).IsPrefix (([2, 0] : List Nat).drop 3) := by decide

-- ll_prefix_5_4_9
example : ([0, 0] : List Nat).IsPrefix ([2, 0] : List Nat) → (([0, 0] : List Nat).drop 9).IsPrefix (([2, 0] : List Nat).drop 9) := by decide

-- ll_prefix_5_5_0
example : ([0, 0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 0] : List Nat).drop 0).IsPrefix (([0, 0] : List Nat).drop 0) := by decide

-- ll_prefix_5_5_1
example : ([0, 0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 0] : List Nat).drop 1).IsPrefix (([0, 0] : List Nat).drop 1) := by decide

-- ll_prefix_5_5_3
example : ([0, 0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 0] : List Nat).drop 3).IsPrefix (([0, 0] : List Nat).drop 3) := by decide

-- ll_prefix_5_5_9
example : ([0, 0] : List Nat).IsPrefix ([0, 0] : List Nat) → (([0, 0] : List Nat).drop 9).IsPrefix (([0, 0] : List Nat).drop 9) := by decide

-- ll_lookup_0_0_0
example : (0 : Nat) < 0 → ((7 : Nat) :: ([] : List Nat))[0-0]? = ([] : List Nat)[0-(0+1)]? := by decide

-- ll_lookup_0_0_1
example : (0 : Nat) < 1 → ((7 : Nat) :: ([] : List Nat))[1-0]? = ([] : List Nat)[1-(0+1)]? := by decide

-- ll_lookup_0_0_3
example : (0 : Nat) < 3 → ((7 : Nat) :: ([] : List Nat))[3-0]? = ([] : List Nat)[3-(0+1)]? := by decide

-- ll_lookup_0_1_2
example : (1 : Nat) < 2 → ((7 : Nat) :: ([] : List Nat))[2-1]? = ([] : List Nat)[2-(1+1)]? := by decide

-- ll_lookup_0_2_8
example : (2 : Nat) < 8 → ((7 : Nat) :: ([] : List Nat))[8-2]? = ([] : List Nat)[8-(2+1)]? := by decide

-- ll_lookup_0_8_2
example : (8 : Nat) < 2 → ((7 : Nat) :: ([] : List Nat))[2-8]? = ([] : List Nat)[2-(8+1)]? := by decide

-- ll_lookup_1_0_0
example : (0 : Nat) < 0 → ((7 : Nat) :: ([0] : List Nat))[0-0]? = ([0] : List Nat)[0-(0+1)]? := by decide

-- ll_lookup_1_0_1
example : (0 : Nat) < 1 → ((7 : Nat) :: ([0] : List Nat))[1-0]? = ([0] : List Nat)[1-(0+1)]? := by decide

-- ll_lookup_1_0_3
example : (0 : Nat) < 3 → ((7 : Nat) :: ([0] : List Nat))[3-0]? = ([0] : List Nat)[3-(0+1)]? := by decide

-- ll_lookup_1_1_2
example : (1 : Nat) < 2 → ((7 : Nat) :: ([0] : List Nat))[2-1]? = ([0] : List Nat)[2-(1+1)]? := by decide

-- ll_lookup_1_2_8
example : (2 : Nat) < 8 → ((7 : Nat) :: ([0] : List Nat))[8-2]? = ([0] : List Nat)[8-(2+1)]? := by decide

-- ll_lookup_1_8_2
example : (8 : Nat) < 2 → ((7 : Nat) :: ([0] : List Nat))[2-8]? = ([0] : List Nat)[2-(8+1)]? := by decide

-- ll_lookup_2_0_0
example : (0 : Nat) < 0 → ((7 : Nat) :: ([0, 1] : List Nat))[0-0]? = ([0, 1] : List Nat)[0-(0+1)]? := by decide

-- ll_lookup_2_0_1
example : (0 : Nat) < 1 → ((7 : Nat) :: ([0, 1] : List Nat))[1-0]? = ([0, 1] : List Nat)[1-(0+1)]? := by decide

-- ll_lookup_2_0_3
example : (0 : Nat) < 3 → ((7 : Nat) :: ([0, 1] : List Nat))[3-0]? = ([0, 1] : List Nat)[3-(0+1)]? := by decide

-- ll_lookup_2_1_2
example : (1 : Nat) < 2 → ((7 : Nat) :: ([0, 1] : List Nat))[2-1]? = ([0, 1] : List Nat)[2-(1+1)]? := by decide

-- ll_lookup_2_2_8
example : (2 : Nat) < 8 → ((7 : Nat) :: ([0, 1] : List Nat))[8-2]? = ([0, 1] : List Nat)[8-(2+1)]? := by decide

-- ll_lookup_2_8_2
example : (8 : Nat) < 2 → ((7 : Nat) :: ([0, 1] : List Nat))[2-8]? = ([0, 1] : List Nat)[2-(8+1)]? := by decide

-- ll_lookup_3_0_0
example : (0 : Nat) < 0 → ((7 : Nat) :: ([0, 1, 2] : List Nat))[0-0]? = ([0, 1, 2] : List Nat)[0-(0+1)]? := by decide

-- ll_lookup_3_0_1
example : (0 : Nat) < 1 → ((7 : Nat) :: ([0, 1, 2] : List Nat))[1-0]? = ([0, 1, 2] : List Nat)[1-(0+1)]? := by decide

-- ll_lookup_3_0_3
example : (0 : Nat) < 3 → ((7 : Nat) :: ([0, 1, 2] : List Nat))[3-0]? = ([0, 1, 2] : List Nat)[3-(0+1)]? := by decide

-- ll_lookup_3_1_2
example : (1 : Nat) < 2 → ((7 : Nat) :: ([0, 1, 2] : List Nat))[2-1]? = ([0, 1, 2] : List Nat)[2-(1+1)]? := by decide

-- ll_lookup_3_2_8
example : (2 : Nat) < 8 → ((7 : Nat) :: ([0, 1, 2] : List Nat))[8-2]? = ([0, 1, 2] : List Nat)[8-(2+1)]? := by decide

-- ll_lookup_3_8_2
example : (8 : Nat) < 2 → ((7 : Nat) :: ([0, 1, 2] : List Nat))[2-8]? = ([0, 1, 2] : List Nat)[2-(8+1)]? := by decide

-- ll_lookup_4_0_0
example : (0 : Nat) < 0 → ((7 : Nat) :: ([2, 0] : List Nat))[0-0]? = ([2, 0] : List Nat)[0-(0+1)]? := by decide

-- ll_lookup_4_0_1
example : (0 : Nat) < 1 → ((7 : Nat) :: ([2, 0] : List Nat))[1-0]? = ([2, 0] : List Nat)[1-(0+1)]? := by decide

-- ll_lookup_4_0_3
example : (0 : Nat) < 3 → ((7 : Nat) :: ([2, 0] : List Nat))[3-0]? = ([2, 0] : List Nat)[3-(0+1)]? := by decide

-- ll_lookup_4_1_2
example : (1 : Nat) < 2 → ((7 : Nat) :: ([2, 0] : List Nat))[2-1]? = ([2, 0] : List Nat)[2-(1+1)]? := by decide

-- ll_lookup_4_2_8
example : (2 : Nat) < 8 → ((7 : Nat) :: ([2, 0] : List Nat))[8-2]? = ([2, 0] : List Nat)[8-(2+1)]? := by decide

-- ll_lookup_4_8_2
example : (8 : Nat) < 2 → ((7 : Nat) :: ([2, 0] : List Nat))[2-8]? = ([2, 0] : List Nat)[2-(8+1)]? := by decide

-- ll_lookup_5_0_0
example : (0 : Nat) < 0 → ((7 : Nat) :: ([0, 0] : List Nat))[0-0]? = ([0, 0] : List Nat)[0-(0+1)]? := by decide

-- ll_lookup_5_0_1
example : (0 : Nat) < 1 → ((7 : Nat) :: ([0, 0] : List Nat))[1-0]? = ([0, 0] : List Nat)[1-(0+1)]? := by decide

-- ll_lookup_5_0_3
example : (0 : Nat) < 3 → ((7 : Nat) :: ([0, 0] : List Nat))[3-0]? = ([0, 0] : List Nat)[3-(0+1)]? := by decide

-- ll_lookup_5_1_2
example : (1 : Nat) < 2 → ((7 : Nat) :: ([0, 0] : List Nat))[2-1]? = ([0, 0] : List Nat)[2-(1+1)]? := by decide

-- ll_lookup_5_2_8
example : (2 : Nat) < 8 → ((7 : Nat) :: ([0, 0] : List Nat))[8-2]? = ([0, 0] : List Nat)[8-(2+1)]? := by decide

-- ll_lookup_5_8_2
example : (8 : Nat) < 2 → ((7 : Nat) :: ([0, 0] : List Nat))[2-8]? = ([0, 0] : List Nat)[2-(8+1)]? := by decide

-- ll_even_0_0
example : (0 : Nat) % 2 = 0 ∧ (0 : Nat) % 2 = 0 ∧ (0 : Nat) / 2 = (0 : Nat) / 2 → (0 : Nat) = 0 := by decide

-- ll_even_0_1
example : (0 : Nat) % 2 = 0 ∧ (1 : Nat) % 2 = 0 ∧ (0 : Nat) / 2 = (1 : Nat) / 2 → (0 : Nat) = 1 := by decide

-- ll_even_0_2
example : (0 : Nat) % 2 = 0 ∧ (2 : Nat) % 2 = 0 ∧ (0 : Nat) / 2 = (2 : Nat) / 2 → (0 : Nat) = 2 := by decide

-- ll_even_0_3
example : (0 : Nat) % 2 = 0 ∧ (3 : Nat) % 2 = 0 ∧ (0 : Nat) / 2 = (3 : Nat) / 2 → (0 : Nat) = 3 := by decide

-- ll_even_0_4
example : (0 : Nat) % 2 = 0 ∧ (4 : Nat) % 2 = 0 ∧ (0 : Nat) / 2 = (4 : Nat) / 2 → (0 : Nat) = 4 := by decide

-- ll_even_0_5
example : (0 : Nat) % 2 = 0 ∧ (6 : Nat) % 2 = 0 ∧ (0 : Nat) / 2 = (6 : Nat) / 2 → (0 : Nat) = 6 := by decide

-- ll_even_0_6
example : (0 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) % 2 = 0 ∧ (0 : Nat) / 2 = (1208925819614629174706176 : Nat) / 2 → (0 : Nat) = 1208925819614629174706176 := by decide

-- ll_even_0_7
example : (0 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) % 2 = 0 ∧ (0 : Nat) / 2 = (1208925819614629174706178 : Nat) / 2 → (0 : Nat) = 1208925819614629174706178 := by decide

-- ll_even_1_0
example : (1 : Nat) % 2 = 0 ∧ (0 : Nat) % 2 = 0 ∧ (1 : Nat) / 2 = (0 : Nat) / 2 → (1 : Nat) = 0 := by decide

-- ll_even_1_1
example : (1 : Nat) % 2 = 0 ∧ (1 : Nat) % 2 = 0 ∧ (1 : Nat) / 2 = (1 : Nat) / 2 → (1 : Nat) = 1 := by decide

-- ll_even_1_2
example : (1 : Nat) % 2 = 0 ∧ (2 : Nat) % 2 = 0 ∧ (1 : Nat) / 2 = (2 : Nat) / 2 → (1 : Nat) = 2 := by decide

-- ll_even_1_3
example : (1 : Nat) % 2 = 0 ∧ (3 : Nat) % 2 = 0 ∧ (1 : Nat) / 2 = (3 : Nat) / 2 → (1 : Nat) = 3 := by decide

-- ll_even_1_4
example : (1 : Nat) % 2 = 0 ∧ (4 : Nat) % 2 = 0 ∧ (1 : Nat) / 2 = (4 : Nat) / 2 → (1 : Nat) = 4 := by decide

-- ll_even_1_5
example : (1 : Nat) % 2 = 0 ∧ (6 : Nat) % 2 = 0 ∧ (1 : Nat) / 2 = (6 : Nat) / 2 → (1 : Nat) = 6 := by decide

-- ll_even_1_6
example : (1 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) % 2 = 0 ∧ (1 : Nat) / 2 = (1208925819614629174706176 : Nat) / 2 → (1 : Nat) = 1208925819614629174706176 := by decide

-- ll_even_1_7
example : (1 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) % 2 = 0 ∧ (1 : Nat) / 2 = (1208925819614629174706178 : Nat) / 2 → (1 : Nat) = 1208925819614629174706178 := by decide

-- ll_even_2_0
example : (2 : Nat) % 2 = 0 ∧ (0 : Nat) % 2 = 0 ∧ (2 : Nat) / 2 = (0 : Nat) / 2 → (2 : Nat) = 0 := by decide

-- ll_even_2_1
example : (2 : Nat) % 2 = 0 ∧ (1 : Nat) % 2 = 0 ∧ (2 : Nat) / 2 = (1 : Nat) / 2 → (2 : Nat) = 1 := by decide

-- ll_even_2_2
example : (2 : Nat) % 2 = 0 ∧ (2 : Nat) % 2 = 0 ∧ (2 : Nat) / 2 = (2 : Nat) / 2 → (2 : Nat) = 2 := by decide

-- ll_even_2_3
example : (2 : Nat) % 2 = 0 ∧ (3 : Nat) % 2 = 0 ∧ (2 : Nat) / 2 = (3 : Nat) / 2 → (2 : Nat) = 3 := by decide

-- ll_even_2_4
example : (2 : Nat) % 2 = 0 ∧ (4 : Nat) % 2 = 0 ∧ (2 : Nat) / 2 = (4 : Nat) / 2 → (2 : Nat) = 4 := by decide

-- ll_even_2_5
example : (2 : Nat) % 2 = 0 ∧ (6 : Nat) % 2 = 0 ∧ (2 : Nat) / 2 = (6 : Nat) / 2 → (2 : Nat) = 6 := by decide

-- ll_even_2_6
example : (2 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) % 2 = 0 ∧ (2 : Nat) / 2 = (1208925819614629174706176 : Nat) / 2 → (2 : Nat) = 1208925819614629174706176 := by decide

-- ll_even_2_7
example : (2 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) % 2 = 0 ∧ (2 : Nat) / 2 = (1208925819614629174706178 : Nat) / 2 → (2 : Nat) = 1208925819614629174706178 := by decide

-- ll_even_3_0
example : (3 : Nat) % 2 = 0 ∧ (0 : Nat) % 2 = 0 ∧ (3 : Nat) / 2 = (0 : Nat) / 2 → (3 : Nat) = 0 := by decide

-- ll_even_3_1
example : (3 : Nat) % 2 = 0 ∧ (1 : Nat) % 2 = 0 ∧ (3 : Nat) / 2 = (1 : Nat) / 2 → (3 : Nat) = 1 := by decide

-- ll_even_3_2
example : (3 : Nat) % 2 = 0 ∧ (2 : Nat) % 2 = 0 ∧ (3 : Nat) / 2 = (2 : Nat) / 2 → (3 : Nat) = 2 := by decide

-- ll_even_3_3
example : (3 : Nat) % 2 = 0 ∧ (3 : Nat) % 2 = 0 ∧ (3 : Nat) / 2 = (3 : Nat) / 2 → (3 : Nat) = 3 := by decide

-- ll_even_3_4
example : (3 : Nat) % 2 = 0 ∧ (4 : Nat) % 2 = 0 ∧ (3 : Nat) / 2 = (4 : Nat) / 2 → (3 : Nat) = 4 := by decide

-- ll_even_3_5
example : (3 : Nat) % 2 = 0 ∧ (6 : Nat) % 2 = 0 ∧ (3 : Nat) / 2 = (6 : Nat) / 2 → (3 : Nat) = 6 := by decide

-- ll_even_3_6
example : (3 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) % 2 = 0 ∧ (3 : Nat) / 2 = (1208925819614629174706176 : Nat) / 2 → (3 : Nat) = 1208925819614629174706176 := by decide

-- ll_even_3_7
example : (3 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) % 2 = 0 ∧ (3 : Nat) / 2 = (1208925819614629174706178 : Nat) / 2 → (3 : Nat) = 1208925819614629174706178 := by decide

-- ll_even_4_0
example : (4 : Nat) % 2 = 0 ∧ (0 : Nat) % 2 = 0 ∧ (4 : Nat) / 2 = (0 : Nat) / 2 → (4 : Nat) = 0 := by decide

-- ll_even_4_1
example : (4 : Nat) % 2 = 0 ∧ (1 : Nat) % 2 = 0 ∧ (4 : Nat) / 2 = (1 : Nat) / 2 → (4 : Nat) = 1 := by decide

-- ll_even_4_2
example : (4 : Nat) % 2 = 0 ∧ (2 : Nat) % 2 = 0 ∧ (4 : Nat) / 2 = (2 : Nat) / 2 → (4 : Nat) = 2 := by decide

-- ll_even_4_3
example : (4 : Nat) % 2 = 0 ∧ (3 : Nat) % 2 = 0 ∧ (4 : Nat) / 2 = (3 : Nat) / 2 → (4 : Nat) = 3 := by decide

-- ll_even_4_4
example : (4 : Nat) % 2 = 0 ∧ (4 : Nat) % 2 = 0 ∧ (4 : Nat) / 2 = (4 : Nat) / 2 → (4 : Nat) = 4 := by decide

-- ll_even_4_5
example : (4 : Nat) % 2 = 0 ∧ (6 : Nat) % 2 = 0 ∧ (4 : Nat) / 2 = (6 : Nat) / 2 → (4 : Nat) = 6 := by decide

-- ll_even_4_6
example : (4 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) % 2 = 0 ∧ (4 : Nat) / 2 = (1208925819614629174706176 : Nat) / 2 → (4 : Nat) = 1208925819614629174706176 := by decide

-- ll_even_4_7
example : (4 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) % 2 = 0 ∧ (4 : Nat) / 2 = (1208925819614629174706178 : Nat) / 2 → (4 : Nat) = 1208925819614629174706178 := by decide

-- ll_even_5_0
example : (6 : Nat) % 2 = 0 ∧ (0 : Nat) % 2 = 0 ∧ (6 : Nat) / 2 = (0 : Nat) / 2 → (6 : Nat) = 0 := by decide

-- ll_even_5_1
example : (6 : Nat) % 2 = 0 ∧ (1 : Nat) % 2 = 0 ∧ (6 : Nat) / 2 = (1 : Nat) / 2 → (6 : Nat) = 1 := by decide

-- ll_even_5_2
example : (6 : Nat) % 2 = 0 ∧ (2 : Nat) % 2 = 0 ∧ (6 : Nat) / 2 = (2 : Nat) / 2 → (6 : Nat) = 2 := by decide

-- ll_even_5_3
example : (6 : Nat) % 2 = 0 ∧ (3 : Nat) % 2 = 0 ∧ (6 : Nat) / 2 = (3 : Nat) / 2 → (6 : Nat) = 3 := by decide

-- ll_even_5_4
example : (6 : Nat) % 2 = 0 ∧ (4 : Nat) % 2 = 0 ∧ (6 : Nat) / 2 = (4 : Nat) / 2 → (6 : Nat) = 4 := by decide

-- ll_even_5_5
example : (6 : Nat) % 2 = 0 ∧ (6 : Nat) % 2 = 0 ∧ (6 : Nat) / 2 = (6 : Nat) / 2 → (6 : Nat) = 6 := by decide

-- ll_even_5_6
example : (6 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) % 2 = 0 ∧ (6 : Nat) / 2 = (1208925819614629174706176 : Nat) / 2 → (6 : Nat) = 1208925819614629174706176 := by decide

-- ll_even_5_7
example : (6 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) % 2 = 0 ∧ (6 : Nat) / 2 = (1208925819614629174706178 : Nat) / 2 → (6 : Nat) = 1208925819614629174706178 := by decide

-- ll_even_6_0
example : (1208925819614629174706176 : Nat) % 2 = 0 ∧ (0 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) / 2 = (0 : Nat) / 2 → (1208925819614629174706176 : Nat) = 0 := by decide

-- ll_even_6_1
example : (1208925819614629174706176 : Nat) % 2 = 0 ∧ (1 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) / 2 = (1 : Nat) / 2 → (1208925819614629174706176 : Nat) = 1 := by decide

-- ll_even_6_2
example : (1208925819614629174706176 : Nat) % 2 = 0 ∧ (2 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) / 2 = (2 : Nat) / 2 → (1208925819614629174706176 : Nat) = 2 := by decide

-- ll_even_6_3
example : (1208925819614629174706176 : Nat) % 2 = 0 ∧ (3 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) / 2 = (3 : Nat) / 2 → (1208925819614629174706176 : Nat) = 3 := by decide

-- ll_even_6_4
example : (1208925819614629174706176 : Nat) % 2 = 0 ∧ (4 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) / 2 = (4 : Nat) / 2 → (1208925819614629174706176 : Nat) = 4 := by decide

-- ll_even_6_5
example : (1208925819614629174706176 : Nat) % 2 = 0 ∧ (6 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) / 2 = (6 : Nat) / 2 → (1208925819614629174706176 : Nat) = 6 := by decide

-- ll_even_6_6
example : (1208925819614629174706176 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) / 2 = (1208925819614629174706176 : Nat) / 2 → (1208925819614629174706176 : Nat) = 1208925819614629174706176 := by decide

-- ll_even_6_7
example : (1208925819614629174706176 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) / 2 = (1208925819614629174706178 : Nat) / 2 → (1208925819614629174706176 : Nat) = 1208925819614629174706178 := by decide

-- ll_even_7_0
example : (1208925819614629174706178 : Nat) % 2 = 0 ∧ (0 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) / 2 = (0 : Nat) / 2 → (1208925819614629174706178 : Nat) = 0 := by decide

-- ll_even_7_1
example : (1208925819614629174706178 : Nat) % 2 = 0 ∧ (1 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) / 2 = (1 : Nat) / 2 → (1208925819614629174706178 : Nat) = 1 := by decide

-- ll_even_7_2
example : (1208925819614629174706178 : Nat) % 2 = 0 ∧ (2 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) / 2 = (2 : Nat) / 2 → (1208925819614629174706178 : Nat) = 2 := by decide

-- ll_even_7_3
example : (1208925819614629174706178 : Nat) % 2 = 0 ∧ (3 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) / 2 = (3 : Nat) / 2 → (1208925819614629174706178 : Nat) = 3 := by decide

-- ll_even_7_4
example : (1208925819614629174706178 : Nat) % 2 = 0 ∧ (4 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) / 2 = (4 : Nat) / 2 → (1208925819614629174706178 : Nat) = 4 := by decide

-- ll_even_7_5
example : (1208925819614629174706178 : Nat) % 2 = 0 ∧ (6 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) / 2 = (6 : Nat) / 2 → (1208925819614629174706178 : Nat) = 6 := by decide

-- ll_even_7_6
example : (1208925819614629174706178 : Nat) % 2 = 0 ∧ (1208925819614629174706176 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) / 2 = (1208925819614629174706176 : Nat) / 2 → (1208925819614629174706178 : Nat) = 1208925819614629174706176 := by decide

-- ll_even_7_7
example : (1208925819614629174706178 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) % 2 = 0 ∧ (1208925819614629174706178 : Nat) / 2 = (1208925819614629174706178 : Nat) / 2 → (1208925819614629174706178 : Nat) = 1208925819614629174706178 := by decide


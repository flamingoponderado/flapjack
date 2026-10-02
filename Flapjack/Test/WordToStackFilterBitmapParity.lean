import Flapjack.Compiler.Backend.WordToStack.Proofs.FilterBitmap
open Flapjack.StackSem Flapjack.Compiler.Backend.WordToStack Flapjack.WordToStackProofs

-- fb_output_0_0
example : filterBitmap [] ([] : List Nat) = some (([] : List Nat),([] : List Nat)) := by decide

-- fb_pair_output_0_0
example : filterBitmap [] ([] : List (Nat × Nat)) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_0_0
example : ([] : List Nat).length ≤ 0 ∧ 0 ≤ ([] : List Nat).length ∧ ∀ x ∈ ([] : List Nat), x ∈ ([] : List Nat) := by decide

-- fb_index_0_0_0
example : filterBitmap [] (indexList ([] : List Nat) 0) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_0_0_7
example : filterBitmap [] (indexList ([] : List Nat) 7) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_0_1
example : filterBitmap [] ([3] : List Nat) = some (([] : List Nat),([3] : List Nat)) := by decide

-- fb_pair_output_0_1
example : filterBitmap [] ([(3, 96)] : List (Nat × Nat)) = some (([] : List (Nat × Nat)),([(3, 96)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_0_1
example : ([] : List Nat).length ≤ 0 ∧ 0 ≤ ([3] : List Nat).length ∧ ∀ x ∈ ([] : List Nat), x ∈ ([3] : List Nat) := by decide

-- fb_index_0_1_0
example : filterBitmap [] (indexList ([] : List Nat) 0) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_0_1_7
example : filterBitmap [] (indexList ([] : List Nat) 7) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_0_2
example : filterBitmap [] ([2, 5] : List Nat) = some (([] : List Nat),([2, 5] : List Nat)) := by decide

-- fb_pair_output_0_2
example : filterBitmap [] ([(2, 97), (5, 94)] : List (Nat × Nat)) = some (([] : List (Nat × Nat)),([(2, 97), (5, 94)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_0_2
example : ([] : List Nat).length ≤ 0 ∧ 0 ≤ ([2, 5] : List Nat).length ∧ ∀ x ∈ ([] : List Nat), x ∈ ([2, 5] : List Nat) := by decide

-- fb_index_0_2_0
example : filterBitmap [] (indexList ([] : List Nat) 0) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_0_2_7
example : filterBitmap [] (indexList ([] : List Nat) 7) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_0_3
example : filterBitmap [] ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),([8, 3, 6, 1] : List Nat)) := by decide

-- fb_pair_output_0_3
example : filterBitmap [] ([(8, 91), (3, 96), (6, 93), (1, 98)] : List (Nat × Nat)) = some (([] : List (Nat × Nat)),([(8, 91), (3, 96), (6, 93), (1, 98)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_0_3
example : ([] : List Nat).length ≤ 0 ∧ 0 ≤ ([8, 3, 6, 1] : List Nat).length ∧ ∀ x ∈ ([] : List Nat), x ∈ ([8, 3, 6, 1] : List Nat) := by decide

-- fb_index_0_3_0
example : filterBitmap [] (indexList ([] : List Nat) 0) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_0_3_7
example : filterBitmap [] (indexList ([] : List Nat) 7) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_zip_reconstruct_0
example : filterBitmap [] ([] : List Nat) = some (((([] : List Nat).zip []).filter (fun p => p.2)).map Prod.fst, []) := by decide

-- fb_output_1_0
example : filterBitmap [false] ([] : List Nat) = none := by decide

-- fb_pair_output_1_0
example : filterBitmap [false] ([] : List (Nat × Nat)) = none := by decide

-- fb_index_1_0_0
example : filterBitmap [false] (indexList ([] : List Nat) 0) = none := by decide

-- fb_index_1_0_7
example : filterBitmap [false] (indexList ([] : List Nat) 7) = none := by decide

-- fb_output_1_1
example : filterBitmap [false] ([3] : List Nat) = some (([] : List Nat),([] : List Nat)) := by decide

-- fb_pair_output_1_1
example : filterBitmap [false] ([(3, 96)] : List (Nat × Nat)) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_1_1
example : ([] : List Nat).length ≤ 1 ∧ 1 ≤ ([3] : List Nat).length ∧ ∀ x ∈ ([] : List Nat), x ∈ ([3] : List Nat) := by decide

-- fb_index_1_1_0
example : filterBitmap [false] (indexList ([3] : List Nat) 0) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_1_1_7
example : filterBitmap [false] (indexList ([3] : List Nat) 7) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_1_2
example : filterBitmap [false] ([2, 5] : List Nat) = some (([] : List Nat),([5] : List Nat)) := by decide

-- fb_pair_output_1_2
example : filterBitmap [false] ([(2, 97), (5, 94)] : List (Nat × Nat)) = some (([] : List (Nat × Nat)),([(5, 94)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_1_2
example : ([] : List Nat).length ≤ 1 ∧ 1 ≤ ([2, 5] : List Nat).length ∧ ∀ x ∈ ([] : List Nat), x ∈ ([2, 5] : List Nat) := by decide

-- fb_index_1_2_0
example : filterBitmap [false] (indexList ([2] : List Nat) 0) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_1_2_7
example : filterBitmap [false] (indexList ([2] : List Nat) 7) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_1_3
example : filterBitmap [false] ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- fb_pair_output_1_3
example : filterBitmap [false] ([(8, 91), (3, 96), (6, 93), (1, 98)] : List (Nat × Nat)) = some (([] : List (Nat × Nat)),([(3, 96), (6, 93), (1, 98)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_1_3
example : ([] : List Nat).length ≤ 1 ∧ 1 ≤ ([8, 3, 6, 1] : List Nat).length ∧ ∀ x ∈ ([] : List Nat), x ∈ ([8, 3, 6, 1] : List Nat) := by decide

-- fb_index_1_3_0
example : filterBitmap [false] (indexList ([8] : List Nat) 0) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_1_3_7
example : filterBitmap [false] (indexList ([8] : List Nat) 7) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_zip_reconstruct_1
example : filterBitmap [false] ([0] : List Nat) = some (((([0] : List Nat).zip [false]).filter (fun p => p.2)).map Prod.fst, []) := by decide

-- fb_output_2_0
example : filterBitmap [true] ([] : List Nat) = none := by decide

-- fb_pair_output_2_0
example : filterBitmap [true] ([] : List (Nat × Nat)) = none := by decide

-- fb_index_2_0_0
example : filterBitmap [true] (indexList ([] : List Nat) 0) = none := by decide

-- fb_index_2_0_7
example : filterBitmap [true] (indexList ([] : List Nat) 7) = none := by decide

-- fb_output_2_1
example : filterBitmap [true] ([3] : List Nat) = some (([3] : List Nat),([] : List Nat)) := by decide

-- fb_pair_output_2_1
example : filterBitmap [true] ([(3, 96)] : List (Nat × Nat)) = some (([(3, 96)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_2_1
example : ([3] : List Nat).length ≤ 1 ∧ 1 ≤ ([3] : List Nat).length ∧ ∀ x ∈ ([3] : List Nat), x ∈ ([3] : List Nat) := by decide

-- fb_index_2_1_0
example : filterBitmap [true] (indexList ([3] : List Nat) 0) = some (([(0, 3)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_2_1_7
example : filterBitmap [true] (indexList ([3] : List Nat) 7) = some (([(7, 3)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_2_2
example : filterBitmap [true] ([2, 5] : List Nat) = some (([2] : List Nat),([5] : List Nat)) := by decide

-- fb_pair_output_2_2
example : filterBitmap [true] ([(2, 97), (5, 94)] : List (Nat × Nat)) = some (([(2, 97)] : List (Nat × Nat)),([(5, 94)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_2_2
example : ([2] : List Nat).length ≤ 1 ∧ 1 ≤ ([2, 5] : List Nat).length ∧ ∀ x ∈ ([2] : List Nat), x ∈ ([2, 5] : List Nat) := by decide

-- fb_index_2_2_0
example : filterBitmap [true] (indexList ([2] : List Nat) 0) = some (([(0, 2)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_2_2_7
example : filterBitmap [true] (indexList ([2] : List Nat) 7) = some (([(7, 2)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_2_3
example : filterBitmap [true] ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- fb_pair_output_2_3
example : filterBitmap [true] ([(8, 91), (3, 96), (6, 93), (1, 98)] : List (Nat × Nat)) = some (([(8, 91)] : List (Nat × Nat)),([(3, 96), (6, 93), (1, 98)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_2_3
example : ([8] : List Nat).length ≤ 1 ∧ 1 ≤ ([8, 3, 6, 1] : List Nat).length ∧ ∀ x ∈ ([8] : List Nat), x ∈ ([8, 3, 6, 1] : List Nat) := by decide

-- fb_index_2_3_0
example : filterBitmap [true] (indexList ([8] : List Nat) 0) = some (([(0, 8)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_2_3_7
example : filterBitmap [true] (indexList ([8] : List Nat) 7) = some (([(7, 8)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_zip_reconstruct_2
example : filterBitmap [true] ([0] : List Nat) = some (((([0] : List Nat).zip [true]).filter (fun p => p.2)).map Prod.fst, []) := by decide

-- fb_output_3_0
example : filterBitmap [false, false] ([] : List Nat) = none := by decide

-- fb_pair_output_3_0
example : filterBitmap [false, false] ([] : List (Nat × Nat)) = none := by decide

-- fb_index_3_0_0
example : filterBitmap [false, false] (indexList ([] : List Nat) 0) = none := by decide

-- fb_index_3_0_7
example : filterBitmap [false, false] (indexList ([] : List Nat) 7) = none := by decide

-- fb_output_3_1
example : filterBitmap [false, false] ([3] : List Nat) = none := by decide

-- fb_pair_output_3_1
example : filterBitmap [false, false] ([(3, 96)] : List (Nat × Nat)) = none := by decide

-- fb_index_3_1_0
example : filterBitmap [false, false] (indexList ([3] : List Nat) 0) = none := by decide

-- fb_index_3_1_7
example : filterBitmap [false, false] (indexList ([3] : List Nat) 7) = none := by decide

-- fb_output_3_2
example : filterBitmap [false, false] ([2, 5] : List Nat) = some (([] : List Nat),([] : List Nat)) := by decide

-- fb_pair_output_3_2
example : filterBitmap [false, false] ([(2, 97), (5, 94)] : List (Nat × Nat)) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_3_2
example : ([] : List Nat).length ≤ 2 ∧ 2 ≤ ([2, 5] : List Nat).length ∧ ∀ x ∈ ([] : List Nat), x ∈ ([2, 5] : List Nat) := by decide

-- fb_index_3_2_0
example : filterBitmap [false, false] (indexList ([2, 5] : List Nat) 0) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_3_2_7
example : filterBitmap [false, false] (indexList ([2, 5] : List Nat) 7) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_3_3
example : filterBitmap [false, false] ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),([6, 1] : List Nat)) := by decide

-- fb_pair_output_3_3
example : filterBitmap [false, false] ([(8, 91), (3, 96), (6, 93), (1, 98)] : List (Nat × Nat)) = some (([] : List (Nat × Nat)),([(6, 93), (1, 98)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_3_3
example : ([] : List Nat).length ≤ 2 ∧ 2 ≤ ([8, 3, 6, 1] : List Nat).length ∧ ∀ x ∈ ([] : List Nat), x ∈ ([8, 3, 6, 1] : List Nat) := by decide

-- fb_index_3_3_0
example : filterBitmap [false, false] (indexList ([8, 3] : List Nat) 0) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_3_3_7
example : filterBitmap [false, false] (indexList ([8, 3] : List Nat) 7) = some (([] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_zip_reconstruct_3
example : filterBitmap [false, false] ([0, 1] : List Nat) = some (((([0, 1] : List Nat).zip [false, false]).filter (fun p => p.2)).map Prod.fst, []) := by decide

-- fb_output_4_0
example : filterBitmap [true, false] ([] : List Nat) = none := by decide

-- fb_pair_output_4_0
example : filterBitmap [true, false] ([] : List (Nat × Nat)) = none := by decide

-- fb_index_4_0_0
example : filterBitmap [true, false] (indexList ([] : List Nat) 0) = none := by decide

-- fb_index_4_0_7
example : filterBitmap [true, false] (indexList ([] : List Nat) 7) = none := by decide

-- fb_output_4_1
example : filterBitmap [true, false] ([3] : List Nat) = none := by decide

-- fb_pair_output_4_1
example : filterBitmap [true, false] ([(3, 96)] : List (Nat × Nat)) = none := by decide

-- fb_index_4_1_0
example : filterBitmap [true, false] (indexList ([3] : List Nat) 0) = none := by decide

-- fb_index_4_1_7
example : filterBitmap [true, false] (indexList ([3] : List Nat) 7) = none := by decide

-- fb_output_4_2
example : filterBitmap [true, false] ([2, 5] : List Nat) = some (([2] : List Nat),([] : List Nat)) := by decide

-- fb_pair_output_4_2
example : filterBitmap [true, false] ([(2, 97), (5, 94)] : List (Nat × Nat)) = some (([(2, 97)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_4_2
example : ([2] : List Nat).length ≤ 2 ∧ 2 ≤ ([2, 5] : List Nat).length ∧ ∀ x ∈ ([2] : List Nat), x ∈ ([2, 5] : List Nat) := by decide

-- fb_index_4_2_0
example : filterBitmap [true, false] (indexList ([2, 5] : List Nat) 0) = some (([(1, 2)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_4_2_7
example : filterBitmap [true, false] (indexList ([2, 5] : List Nat) 7) = some (([(8, 2)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_4_3
example : filterBitmap [true, false] ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),([6, 1] : List Nat)) := by decide

-- fb_pair_output_4_3
example : filterBitmap [true, false] ([(8, 91), (3, 96), (6, 93), (1, 98)] : List (Nat × Nat)) = some (([(8, 91)] : List (Nat × Nat)),([(6, 93), (1, 98)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_4_3
example : ([8] : List Nat).length ≤ 2 ∧ 2 ≤ ([8, 3, 6, 1] : List Nat).length ∧ ∀ x ∈ ([8] : List Nat), x ∈ ([8, 3, 6, 1] : List Nat) := by decide

-- fb_index_4_3_0
example : filterBitmap [true, false] (indexList ([8, 3] : List Nat) 0) = some (([(1, 8)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_4_3_7
example : filterBitmap [true, false] (indexList ([8, 3] : List Nat) 7) = some (([(8, 8)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_zip_reconstruct_4
example : filterBitmap [true, false] ([0, 1] : List Nat) = some (((([0, 1] : List Nat).zip [true, false]).filter (fun p => p.2)).map Prod.fst, []) := by decide

-- fb_output_5_0
example : filterBitmap [false, true] ([] : List Nat) = none := by decide

-- fb_pair_output_5_0
example : filterBitmap [false, true] ([] : List (Nat × Nat)) = none := by decide

-- fb_index_5_0_0
example : filterBitmap [false, true] (indexList ([] : List Nat) 0) = none := by decide

-- fb_index_5_0_7
example : filterBitmap [false, true] (indexList ([] : List Nat) 7) = none := by decide

-- fb_output_5_1
example : filterBitmap [false, true] ([3] : List Nat) = none := by decide

-- fb_pair_output_5_1
example : filterBitmap [false, true] ([(3, 96)] : List (Nat × Nat)) = none := by decide

-- fb_index_5_1_0
example : filterBitmap [false, true] (indexList ([3] : List Nat) 0) = none := by decide

-- fb_index_5_1_7
example : filterBitmap [false, true] (indexList ([3] : List Nat) 7) = none := by decide

-- fb_output_5_2
example : filterBitmap [false, true] ([2, 5] : List Nat) = some (([5] : List Nat),([] : List Nat)) := by decide

-- fb_pair_output_5_2
example : filterBitmap [false, true] ([(2, 97), (5, 94)] : List (Nat × Nat)) = some (([(5, 94)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_5_2
example : ([5] : List Nat).length ≤ 2 ∧ 2 ≤ ([2, 5] : List Nat).length ∧ ∀ x ∈ ([5] : List Nat), x ∈ ([2, 5] : List Nat) := by decide

-- fb_index_5_2_0
example : filterBitmap [false, true] (indexList ([2, 5] : List Nat) 0) = some (([(0, 5)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_5_2_7
example : filterBitmap [false, true] (indexList ([2, 5] : List Nat) 7) = some (([(7, 5)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_5_3
example : filterBitmap [false, true] ([8, 3, 6, 1] : List Nat) = some (([3] : List Nat),([6, 1] : List Nat)) := by decide

-- fb_pair_output_5_3
example : filterBitmap [false, true] ([(8, 91), (3, 96), (6, 93), (1, 98)] : List (Nat × Nat)) = some (([(3, 96)] : List (Nat × Nat)),([(6, 93), (1, 98)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_5_3
example : ([3] : List Nat).length ≤ 2 ∧ 2 ≤ ([8, 3, 6, 1] : List Nat).length ∧ ∀ x ∈ ([3] : List Nat), x ∈ ([8, 3, 6, 1] : List Nat) := by decide

-- fb_index_5_3_0
example : filterBitmap [false, true] (indexList ([8, 3] : List Nat) 0) = some (([(0, 3)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_5_3_7
example : filterBitmap [false, true] (indexList ([8, 3] : List Nat) 7) = some (([(7, 3)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_zip_reconstruct_5
example : filterBitmap [false, true] ([0, 1] : List Nat) = some (((([0, 1] : List Nat).zip [false, true]).filter (fun p => p.2)).map Prod.fst, []) := by decide

-- fb_output_6_0
example : filterBitmap [true, true] ([] : List Nat) = none := by decide

-- fb_pair_output_6_0
example : filterBitmap [true, true] ([] : List (Nat × Nat)) = none := by decide

-- fb_index_6_0_0
example : filterBitmap [true, true] (indexList ([] : List Nat) 0) = none := by decide

-- fb_index_6_0_7
example : filterBitmap [true, true] (indexList ([] : List Nat) 7) = none := by decide

-- fb_output_6_1
example : filterBitmap [true, true] ([3] : List Nat) = none := by decide

-- fb_pair_output_6_1
example : filterBitmap [true, true] ([(3, 96)] : List (Nat × Nat)) = none := by decide

-- fb_index_6_1_0
example : filterBitmap [true, true] (indexList ([3] : List Nat) 0) = none := by decide

-- fb_index_6_1_7
example : filterBitmap [true, true] (indexList ([3] : List Nat) 7) = none := by decide

-- fb_output_6_2
example : filterBitmap [true, true] ([2, 5] : List Nat) = some (([2, 5] : List Nat),([] : List Nat)) := by decide

-- fb_pair_output_6_2
example : filterBitmap [true, true] ([(2, 97), (5, 94)] : List (Nat × Nat)) = some (([(2, 97), (5, 94)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_6_2
example : ([2, 5] : List Nat).length ≤ 2 ∧ 2 ≤ ([2, 5] : List Nat).length ∧ ∀ x ∈ ([2, 5] : List Nat), x ∈ ([2, 5] : List Nat) := by decide

-- fb_index_6_2_0
example : filterBitmap [true, true] (indexList ([2, 5] : List Nat) 0) = some (([(1, 2), (0, 5)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_6_2_7
example : filterBitmap [true, true] (indexList ([2, 5] : List Nat) 7) = some (([(8, 2), (7, 5)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_output_6_3
example : filterBitmap [true, true] ([8, 3, 6, 1] : List Nat) = some (([8, 3] : List Nat),([6, 1] : List Nat)) := by decide

-- fb_pair_output_6_3
example : filterBitmap [true, true] ([(8, 91), (3, 96), (6, 93), (1, 98)] : List (Nat × Nat)) = some (([(8, 91), (3, 96)] : List (Nat × Nat)),([(6, 93), (1, 98)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_6_3
example : ([8, 3] : List Nat).length ≤ 2 ∧ 2 ≤ ([8, 3, 6, 1] : List Nat).length ∧ ∀ x ∈ ([8, 3] : List Nat), x ∈ ([8, 3, 6, 1] : List Nat) := by decide

-- fb_index_6_3_0
example : filterBitmap [true, true] (indexList ([8, 3] : List Nat) 0) = some (([(1, 8), (0, 3)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_6_3_7
example : filterBitmap [true, true] (indexList ([8, 3] : List Nat) 7) = some (([(8, 8), (7, 3)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_zip_reconstruct_6
example : filterBitmap [true, true] ([0, 1] : List Nat) = some (((([0, 1] : List Nat).zip [true, true]).filter (fun p => p.2)).map Prod.fst, []) := by decide

-- fb_output_7_0
example : filterBitmap [true, false, true] ([] : List Nat) = none := by decide

-- fb_pair_output_7_0
example : filterBitmap [true, false, true] ([] : List (Nat × Nat)) = none := by decide

-- fb_index_7_0_0
example : filterBitmap [true, false, true] (indexList ([] : List Nat) 0) = none := by decide

-- fb_index_7_0_7
example : filterBitmap [true, false, true] (indexList ([] : List Nat) 7) = none := by decide

-- fb_output_7_1
example : filterBitmap [true, false, true] ([3] : List Nat) = none := by decide

-- fb_pair_output_7_1
example : filterBitmap [true, false, true] ([(3, 96)] : List (Nat × Nat)) = none := by decide

-- fb_index_7_1_0
example : filterBitmap [true, false, true] (indexList ([3] : List Nat) 0) = none := by decide

-- fb_index_7_1_7
example : filterBitmap [true, false, true] (indexList ([3] : List Nat) 7) = none := by decide

-- fb_output_7_2
example : filterBitmap [true, false, true] ([2, 5] : List Nat) = none := by decide

-- fb_pair_output_7_2
example : filterBitmap [true, false, true] ([(2, 97), (5, 94)] : List (Nat × Nat)) = none := by decide

-- fb_index_7_2_0
example : filterBitmap [true, false, true] (indexList ([2, 5] : List Nat) 0) = none := by decide

-- fb_index_7_2_7
example : filterBitmap [true, false, true] (indexList ([2, 5] : List Nat) 7) = none := by decide

-- fb_output_7_3
example : filterBitmap [true, false, true] ([8, 3, 6, 1] : List Nat) = some (([8, 6] : List Nat),([1] : List Nat)) := by decide

-- fb_pair_output_7_3
example : filterBitmap [true, false, true] ([(8, 91), (3, 96), (6, 93), (1, 98)] : List (Nat × Nat)) = some (([(8, 91), (6, 93)] : List (Nat × Nat)),([(1, 98)] : List (Nat × Nat))) := by decide

-- fb_bounds_mem_7_3
example : ([8, 6] : List Nat).length ≤ 3 ∧ 3 ≤ ([8, 3, 6, 1] : List Nat).length ∧ ∀ x ∈ ([8, 6] : List Nat), x ∈ ([8, 3, 6, 1] : List Nat) := by decide

-- fb_index_7_3_0
example : filterBitmap [true, false, true] (indexList ([8, 3, 6] : List Nat) 0) = some (([(2, 8), (0, 6)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_index_7_3_7
example : filterBitmap [true, false, true] (indexList ([8, 3, 6] : List Nat) 7) = some (([(9, 8), (7, 6)] : List (Nat × Nat)),([] : List (Nat × Nat))) := by decide

-- fb_zip_reconstruct_7
example : filterBitmap [true, false, true] ([0, 1, 2] : List Nat) = some (((([0, 1, 2] : List Nat).zip [true, false, true]).filter (fun p => p.2)).map Prod.fst, []) := by decide


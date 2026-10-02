import Flapjack.Compiler.Backend.WordToStack.Proofs.MapBitmap
open Flapjack.StackSem Flapjack.Compiler.Backend.WordToStack

-- mb_output_0_0_0
example : mapBitmap [] ([] : List Nat) ([] : List Nat) = some (([] : List Nat),([] : List Nat),([] : List Nat)) := by decide

-- mb_output_0_0_1
example : mapBitmap [] ([91] : List Nat) ([] : List Nat) = some (([] : List Nat),([91] : List Nat),([] : List Nat)) := by decide

-- mb_output_0_0_2
example : mapBitmap [] ([91, 92] : List Nat) ([] : List Nat) = some (([] : List Nat),([91, 92] : List Nat),([] : List Nat)) := by decide

-- mb_output_0_0_3
example : mapBitmap [] ([91, 92, 93, 94] : List Nat) ([] : List Nat) = some (([] : List Nat),([91, 92, 93, 94] : List Nat),([] : List Nat)) := by decide

-- mb_success_witness_0_0
example : mapBitmap [] ([] : List Nat) ([] : List Nat) = some (([] : List Nat),[],([] : List Nat)) ∧ filterBitmap [] ([] : List Nat) = some (([] : List Nat),[]) := by decide

-- mb_more_0_0
example : mapBitmap [] (([] : List Nat) ++ ([77, 78] : List Nat)) ([] : List Nat) = some (([] : List Nat),([77, 78] : List Nat),([] : List Nat)) := by decide

-- mb_prefix_suffix_0_0
example : mapBitmap [] (([77, 78] : List Nat).take 0) ([] : List Nat) = some (([] : List Nat),[],([] : List Nat)) ∧ mapBitmap [] ([77, 78] : List Nat) ([] : List Nat) = some (([] : List Nat),([77, 78] : List Nat).drop 0,([] : List Nat)) := by decide

-- mb_output_0_1_0
example : mapBitmap [] ([] : List Nat) ([3] : List Nat) = some (([] : List Nat),([] : List Nat),([3] : List Nat)) := by decide

-- mb_output_0_1_1
example : mapBitmap [] ([91] : List Nat) ([3] : List Nat) = some (([] : List Nat),([91] : List Nat),([3] : List Nat)) := by decide

-- mb_output_0_1_2
example : mapBitmap [] ([91, 92] : List Nat) ([3] : List Nat) = some (([] : List Nat),([91, 92] : List Nat),([3] : List Nat)) := by decide

-- mb_output_0_1_3
example : mapBitmap [] ([91, 92, 93, 94] : List Nat) ([3] : List Nat) = some (([] : List Nat),([91, 92, 93, 94] : List Nat),([3] : List Nat)) := by decide

-- mb_success_witness_0_1
example : mapBitmap [] ([] : List Nat) ([3] : List Nat) = some (([] : List Nat),[],([3] : List Nat)) ∧ filterBitmap [] ([] : List Nat) = some (([] : List Nat),[]) := by decide

-- mb_more_0_1
example : mapBitmap [] (([] : List Nat) ++ ([77, 78] : List Nat)) ([3] : List Nat) = some (([] : List Nat),([77, 78] : List Nat),([3] : List Nat)) := by decide

-- mb_prefix_suffix_0_1
example : mapBitmap [] (([77, 78] : List Nat).take 0) ([3] : List Nat) = some (([] : List Nat),[],([3] : List Nat)) ∧ mapBitmap [] ([77, 78] : List Nat) ([3] : List Nat) = some (([] : List Nat),([77, 78] : List Nat).drop 0,([3] : List Nat)) := by decide

-- mb_output_0_2_0
example : mapBitmap [] ([] : List Nat) ([2, 5] : List Nat) = some (([] : List Nat),([] : List Nat),([2, 5] : List Nat)) := by decide

-- mb_output_0_2_1
example : mapBitmap [] ([91] : List Nat) ([2, 5] : List Nat) = some (([] : List Nat),([91] : List Nat),([2, 5] : List Nat)) := by decide

-- mb_output_0_2_2
example : mapBitmap [] ([91, 92] : List Nat) ([2, 5] : List Nat) = some (([] : List Nat),([91, 92] : List Nat),([2, 5] : List Nat)) := by decide

-- mb_output_0_2_3
example : mapBitmap [] ([91, 92, 93, 94] : List Nat) ([2, 5] : List Nat) = some (([] : List Nat),([91, 92, 93, 94] : List Nat),([2, 5] : List Nat)) := by decide

-- mb_success_witness_0_2
example : mapBitmap [] ([] : List Nat) ([2, 5] : List Nat) = some (([] : List Nat),[],([2, 5] : List Nat)) ∧ filterBitmap [] ([] : List Nat) = some (([] : List Nat),[]) := by decide

-- mb_more_0_2
example : mapBitmap [] (([] : List Nat) ++ ([77, 78] : List Nat)) ([2, 5] : List Nat) = some (([] : List Nat),([77, 78] : List Nat),([2, 5] : List Nat)) := by decide

-- mb_prefix_suffix_0_2
example : mapBitmap [] (([77, 78] : List Nat).take 0) ([2, 5] : List Nat) = some (([] : List Nat),[],([2, 5] : List Nat)) ∧ mapBitmap [] ([77, 78] : List Nat) ([2, 5] : List Nat) = some (([] : List Nat),([77, 78] : List Nat).drop 0,([2, 5] : List Nat)) := by decide

-- mb_output_0_3_0
example : mapBitmap [] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),([] : List Nat),([8, 3, 6, 1] : List Nat)) := by decide

-- mb_output_0_3_1
example : mapBitmap [] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),([91] : List Nat),([8, 3, 6, 1] : List Nat)) := by decide

-- mb_output_0_3_2
example : mapBitmap [] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),([91, 92] : List Nat),([8, 3, 6, 1] : List Nat)) := by decide

-- mb_output_0_3_3
example : mapBitmap [] ([91, 92, 93, 94] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),([91, 92, 93, 94] : List Nat),([8, 3, 6, 1] : List Nat)) := by decide

-- mb_success_witness_0_3
example : mapBitmap [] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),[],([8, 3, 6, 1] : List Nat)) ∧ filterBitmap [] ([] : List Nat) = some (([] : List Nat),[]) := by decide

-- mb_more_0_3
example : mapBitmap [] (([] : List Nat) ++ ([77, 78] : List Nat)) ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),([77, 78] : List Nat),([8, 3, 6, 1] : List Nat)) := by decide

-- mb_prefix_suffix_0_3
example : mapBitmap [] (([77, 78] : List Nat).take 0) ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),[],([8, 3, 6, 1] : List Nat)) ∧ mapBitmap [] ([77, 78] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([] : List Nat),([77, 78] : List Nat).drop 0,([8, 3, 6, 1] : List Nat)) := by decide

-- mb_output_1_0_0
example : mapBitmap [false] ([] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_1_0_1
example : mapBitmap [false] ([91] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_1_0_2
example : mapBitmap [false] ([91, 92] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_1_0_3
example : mapBitmap [false] ([91, 92, 93, 94] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_1_1_0
example : mapBitmap [false] ([] : List Nat) ([3] : List Nat) = some (([3] : List Nat),([] : List Nat),([] : List Nat)) := by decide

-- mb_output_1_1_1
example : mapBitmap [false] ([91] : List Nat) ([3] : List Nat) = some (([3] : List Nat),([91] : List Nat),([] : List Nat)) := by decide

-- mb_output_1_1_2
example : mapBitmap [false] ([91, 92] : List Nat) ([3] : List Nat) = some (([3] : List Nat),([91, 92] : List Nat),([] : List Nat)) := by decide

-- mb_output_1_1_3
example : mapBitmap [false] ([91, 92, 93, 94] : List Nat) ([3] : List Nat) = some (([3] : List Nat),([91, 92, 93, 94] : List Nat),([] : List Nat)) := by decide

-- mb_success_witness_1_1
example : mapBitmap [false] ([] : List Nat) ([3] : List Nat) = some (([3] : List Nat),[],([] : List Nat)) ∧ filterBitmap [false] ([3] : List Nat) = some (([] : List Nat),[]) := by decide

-- mb_more_1_1
example : mapBitmap [false] (([] : List Nat) ++ ([77, 78] : List Nat)) ([3] : List Nat) = some (([3] : List Nat),([77, 78] : List Nat),([] : List Nat)) := by decide

-- mb_prefix_suffix_1_1
example : mapBitmap [false] (([77, 78] : List Nat).take 0) ([3] : List Nat) = some (([3] : List Nat),[],([] : List Nat)) ∧ mapBitmap [false] ([77, 78] : List Nat) ([3] : List Nat) = some (([3] : List Nat),([77, 78] : List Nat).drop 0,([] : List Nat)) := by decide

-- mb_false_slot_1_1_0
example : [false][0]? = some false ∧ ([3] : List Nat)[0]? = some 3 ∧ ([3] : List Nat)[0]? = some 3 := by decide

-- mb_output_1_2_0
example : mapBitmap [false] ([] : List Nat) ([2, 5] : List Nat) = some (([2] : List Nat),([] : List Nat),([5] : List Nat)) := by decide

-- mb_output_1_2_1
example : mapBitmap [false] ([91] : List Nat) ([2, 5] : List Nat) = some (([2] : List Nat),([91] : List Nat),([5] : List Nat)) := by decide

-- mb_output_1_2_2
example : mapBitmap [false] ([91, 92] : List Nat) ([2, 5] : List Nat) = some (([2] : List Nat),([91, 92] : List Nat),([5] : List Nat)) := by decide

-- mb_output_1_2_3
example : mapBitmap [false] ([91, 92, 93, 94] : List Nat) ([2, 5] : List Nat) = some (([2] : List Nat),([91, 92, 93, 94] : List Nat),([5] : List Nat)) := by decide

-- mb_success_witness_1_2
example : mapBitmap [false] ([] : List Nat) ([2, 5] : List Nat) = some (([2] : List Nat),[],([5] : List Nat)) ∧ filterBitmap [false] ([2] : List Nat) = some (([] : List Nat),[]) := by decide

-- mb_more_1_2
example : mapBitmap [false] (([] : List Nat) ++ ([77, 78] : List Nat)) ([2, 5] : List Nat) = some (([2] : List Nat),([77, 78] : List Nat),([5] : List Nat)) := by decide

-- mb_prefix_suffix_1_2
example : mapBitmap [false] (([77, 78] : List Nat).take 0) ([2, 5] : List Nat) = some (([2] : List Nat),[],([5] : List Nat)) ∧ mapBitmap [false] ([77, 78] : List Nat) ([2, 5] : List Nat) = some (([2] : List Nat),([77, 78] : List Nat).drop 0,([5] : List Nat)) := by decide

-- mb_false_slot_1_2_0
example : [false][0]? = some false ∧ ([2] : List Nat)[0]? = some 2 ∧ ([2, 5] : List Nat)[0]? = some 2 := by decide

-- mb_output_1_3_0
example : mapBitmap [false] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),([] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- mb_output_1_3_1
example : mapBitmap [false] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),([91] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- mb_output_1_3_2
example : mapBitmap [false] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),([91, 92] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- mb_output_1_3_3
example : mapBitmap [false] ([91, 92, 93, 94] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),([91, 92, 93, 94] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- mb_success_witness_1_3
example : mapBitmap [false] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),[],([3, 6, 1] : List Nat)) ∧ filterBitmap [false] ([8] : List Nat) = some (([] : List Nat),[]) := by decide

-- mb_more_1_3
example : mapBitmap [false] (([] : List Nat) ++ ([77, 78] : List Nat)) ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),([77, 78] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- mb_prefix_suffix_1_3
example : mapBitmap [false] (([77, 78] : List Nat).take 0) ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),[],([3, 6, 1] : List Nat)) ∧ mapBitmap [false] ([77, 78] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8] : List Nat),([77, 78] : List Nat).drop 0,([3, 6, 1] : List Nat)) := by decide

-- mb_false_slot_1_3_0
example : [false][0]? = some false ∧ ([8] : List Nat)[0]? = some 8 ∧ ([8, 3, 6, 1] : List Nat)[0]? = some 8 := by decide

-- mb_output_2_0_0
example : mapBitmap [true] ([] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_2_0_1
example : mapBitmap [true] ([91] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_2_0_2
example : mapBitmap [true] ([91, 92] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_2_0_3
example : mapBitmap [true] ([91, 92, 93, 94] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_2_1_0
example : mapBitmap [true] ([] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_2_1_1
example : mapBitmap [true] ([91] : List Nat) ([3] : List Nat) = some (([91] : List Nat),([] : List Nat),([] : List Nat)) := by decide

-- mb_output_2_1_2
example : mapBitmap [true] ([91, 92] : List Nat) ([3] : List Nat) = some (([91] : List Nat),([92] : List Nat),([] : List Nat)) := by decide

-- mb_output_2_1_3
example : mapBitmap [true] ([91, 92, 93, 94] : List Nat) ([3] : List Nat) = some (([91] : List Nat),([92, 93, 94] : List Nat),([] : List Nat)) := by decide

-- mb_success_witness_2_1
example : mapBitmap [true] ([91] : List Nat) ([3] : List Nat) = some (([91] : List Nat),[],([] : List Nat)) ∧ filterBitmap [true] ([91] : List Nat) = some (([91] : List Nat),[]) := by decide

-- mb_more_2_1
example : mapBitmap [true] (([91] : List Nat) ++ ([77, 78] : List Nat)) ([3] : List Nat) = some (([91] : List Nat),([77, 78] : List Nat),([] : List Nat)) := by decide

-- mb_prefix_suffix_2_1
example : mapBitmap [true] (([91, 77, 78] : List Nat).take 1) ([3] : List Nat) = some (([91] : List Nat),[],([] : List Nat)) ∧ mapBitmap [true] ([91, 77, 78] : List Nat) ([3] : List Nat) = some (([91] : List Nat),([91, 77, 78] : List Nat).drop 1,([] : List Nat)) := by decide

-- mb_output_2_2_0
example : mapBitmap [true] ([] : List Nat) ([2, 5] : List Nat) = none := by decide

-- mb_output_2_2_1
example : mapBitmap [true] ([91] : List Nat) ([2, 5] : List Nat) = some (([91] : List Nat),([] : List Nat),([5] : List Nat)) := by decide

-- mb_output_2_2_2
example : mapBitmap [true] ([91, 92] : List Nat) ([2, 5] : List Nat) = some (([91] : List Nat),([92] : List Nat),([5] : List Nat)) := by decide

-- mb_output_2_2_3
example : mapBitmap [true] ([91, 92, 93, 94] : List Nat) ([2, 5] : List Nat) = some (([91] : List Nat),([92, 93, 94] : List Nat),([5] : List Nat)) := by decide

-- mb_success_witness_2_2
example : mapBitmap [true] ([91] : List Nat) ([2, 5] : List Nat) = some (([91] : List Nat),[],([5] : List Nat)) ∧ filterBitmap [true] ([91] : List Nat) = some (([91] : List Nat),[]) := by decide

-- mb_more_2_2
example : mapBitmap [true] (([91] : List Nat) ++ ([77, 78] : List Nat)) ([2, 5] : List Nat) = some (([91] : List Nat),([77, 78] : List Nat),([5] : List Nat)) := by decide

-- mb_prefix_suffix_2_2
example : mapBitmap [true] (([91, 77, 78] : List Nat).take 1) ([2, 5] : List Nat) = some (([91] : List Nat),[],([5] : List Nat)) ∧ mapBitmap [true] ([91, 77, 78] : List Nat) ([2, 5] : List Nat) = some (([91] : List Nat),([91, 77, 78] : List Nat).drop 1,([5] : List Nat)) := by decide

-- mb_output_2_3_0
example : mapBitmap [true] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = none := by decide

-- mb_output_2_3_1
example : mapBitmap [true] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91] : List Nat),([] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- mb_output_2_3_2
example : mapBitmap [true] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91] : List Nat),([92] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- mb_output_2_3_3
example : mapBitmap [true] ([91, 92, 93, 94] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91] : List Nat),([92, 93, 94] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- mb_success_witness_2_3
example : mapBitmap [true] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91] : List Nat),[],([3, 6, 1] : List Nat)) ∧ filterBitmap [true] ([91] : List Nat) = some (([91] : List Nat),[]) := by decide

-- mb_more_2_3
example : mapBitmap [true] (([91] : List Nat) ++ ([77, 78] : List Nat)) ([8, 3, 6, 1] : List Nat) = some (([91] : List Nat),([77, 78] : List Nat),([3, 6, 1] : List Nat)) := by decide

-- mb_prefix_suffix_2_3
example : mapBitmap [true] (([91, 77, 78] : List Nat).take 1) ([8, 3, 6, 1] : List Nat) = some (([91] : List Nat),[],([3, 6, 1] : List Nat)) ∧ mapBitmap [true] ([91, 77, 78] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91] : List Nat),([91, 77, 78] : List Nat).drop 1,([3, 6, 1] : List Nat)) := by decide

-- mb_output_3_0_0
example : mapBitmap [false, false] ([] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_3_0_1
example : mapBitmap [false, false] ([91] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_3_0_2
example : mapBitmap [false, false] ([91, 92] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_3_0_3
example : mapBitmap [false, false] ([91, 92, 93, 94] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_3_1_0
example : mapBitmap [false, false] ([] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_3_1_1
example : mapBitmap [false, false] ([91] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_3_1_2
example : mapBitmap [false, false] ([91, 92] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_3_1_3
example : mapBitmap [false, false] ([91, 92, 93, 94] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_3_2_0
example : mapBitmap [false, false] ([] : List Nat) ([2, 5] : List Nat) = some (([2, 5] : List Nat),([] : List Nat),([] : List Nat)) := by decide

-- mb_output_3_2_1
example : mapBitmap [false, false] ([91] : List Nat) ([2, 5] : List Nat) = some (([2, 5] : List Nat),([91] : List Nat),([] : List Nat)) := by decide

-- mb_output_3_2_2
example : mapBitmap [false, false] ([91, 92] : List Nat) ([2, 5] : List Nat) = some (([2, 5] : List Nat),([91, 92] : List Nat),([] : List Nat)) := by decide

-- mb_output_3_2_3
example : mapBitmap [false, false] ([91, 92, 93, 94] : List Nat) ([2, 5] : List Nat) = some (([2, 5] : List Nat),([91, 92, 93, 94] : List Nat),([] : List Nat)) := by decide

-- mb_success_witness_3_2
example : mapBitmap [false, false] ([] : List Nat) ([2, 5] : List Nat) = some (([2, 5] : List Nat),[],([] : List Nat)) ∧ filterBitmap [false, false] ([2, 5] : List Nat) = some (([] : List Nat),[]) := by decide

-- mb_more_3_2
example : mapBitmap [false, false] (([] : List Nat) ++ ([77, 78] : List Nat)) ([2, 5] : List Nat) = some (([2, 5] : List Nat),([77, 78] : List Nat),([] : List Nat)) := by decide

-- mb_prefix_suffix_3_2
example : mapBitmap [false, false] (([77, 78] : List Nat).take 0) ([2, 5] : List Nat) = some (([2, 5] : List Nat),[],([] : List Nat)) ∧ mapBitmap [false, false] ([77, 78] : List Nat) ([2, 5] : List Nat) = some (([2, 5] : List Nat),([77, 78] : List Nat).drop 0,([] : List Nat)) := by decide

-- mb_false_slot_3_2_0
example : [false, false][0]? = some false ∧ ([2, 5] : List Nat)[0]? = some 2 ∧ ([2, 5] : List Nat)[0]? = some 2 := by decide

-- mb_false_slot_3_2_1
example : [false, false][1]? = some false ∧ ([2, 5] : List Nat)[1]? = some 5 ∧ ([2, 5] : List Nat)[1]? = some 5 := by decide

-- mb_output_3_3_0
example : mapBitmap [false, false] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 3] : List Nat),([] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_output_3_3_1
example : mapBitmap [false, false] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 3] : List Nat),([91] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_output_3_3_2
example : mapBitmap [false, false] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 3] : List Nat),([91, 92] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_output_3_3_3
example : mapBitmap [false, false] ([91, 92, 93, 94] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 3] : List Nat),([91, 92, 93, 94] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_success_witness_3_3
example : mapBitmap [false, false] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 3] : List Nat),[],([6, 1] : List Nat)) ∧ filterBitmap [false, false] ([8, 3] : List Nat) = some (([] : List Nat),[]) := by decide

-- mb_more_3_3
example : mapBitmap [false, false] (([] : List Nat) ++ ([77, 78] : List Nat)) ([8, 3, 6, 1] : List Nat) = some (([8, 3] : List Nat),([77, 78] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_prefix_suffix_3_3
example : mapBitmap [false, false] (([77, 78] : List Nat).take 0) ([8, 3, 6, 1] : List Nat) = some (([8, 3] : List Nat),[],([6, 1] : List Nat)) ∧ mapBitmap [false, false] ([77, 78] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 3] : List Nat),([77, 78] : List Nat).drop 0,([6, 1] : List Nat)) := by decide

-- mb_false_slot_3_3_0
example : [false, false][0]? = some false ∧ ([8, 3] : List Nat)[0]? = some 8 ∧ ([8, 3, 6, 1] : List Nat)[0]? = some 8 := by decide

-- mb_false_slot_3_3_1
example : [false, false][1]? = some false ∧ ([8, 3] : List Nat)[1]? = some 3 ∧ ([8, 3, 6, 1] : List Nat)[1]? = some 3 := by decide

-- mb_output_4_0_0
example : mapBitmap [true, false] ([] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_4_0_1
example : mapBitmap [true, false] ([91] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_4_0_2
example : mapBitmap [true, false] ([91, 92] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_4_0_3
example : mapBitmap [true, false] ([91, 92, 93, 94] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_4_1_0
example : mapBitmap [true, false] ([] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_4_1_1
example : mapBitmap [true, false] ([91] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_4_1_2
example : mapBitmap [true, false] ([91, 92] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_4_1_3
example : mapBitmap [true, false] ([91, 92, 93, 94] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_4_2_0
example : mapBitmap [true, false] ([] : List Nat) ([2, 5] : List Nat) = none := by decide

-- mb_output_4_2_1
example : mapBitmap [true, false] ([91] : List Nat) ([2, 5] : List Nat) = some (([91, 5] : List Nat),([] : List Nat),([] : List Nat)) := by decide

-- mb_output_4_2_2
example : mapBitmap [true, false] ([91, 92] : List Nat) ([2, 5] : List Nat) = some (([91, 5] : List Nat),([92] : List Nat),([] : List Nat)) := by decide

-- mb_output_4_2_3
example : mapBitmap [true, false] ([91, 92, 93, 94] : List Nat) ([2, 5] : List Nat) = some (([91, 5] : List Nat),([92, 93, 94] : List Nat),([] : List Nat)) := by decide

-- mb_success_witness_4_2
example : mapBitmap [true, false] ([91] : List Nat) ([2, 5] : List Nat) = some (([91, 5] : List Nat),[],([] : List Nat)) ∧ filterBitmap [true, false] ([91, 5] : List Nat) = some (([91] : List Nat),[]) := by decide

-- mb_more_4_2
example : mapBitmap [true, false] (([91] : List Nat) ++ ([77, 78] : List Nat)) ([2, 5] : List Nat) = some (([91, 5] : List Nat),([77, 78] : List Nat),([] : List Nat)) := by decide

-- mb_prefix_suffix_4_2
example : mapBitmap [true, false] (([91, 77, 78] : List Nat).take 1) ([2, 5] : List Nat) = some (([91, 5] : List Nat),[],([] : List Nat)) ∧ mapBitmap [true, false] ([91, 77, 78] : List Nat) ([2, 5] : List Nat) = some (([91, 5] : List Nat),([91, 77, 78] : List Nat).drop 1,([] : List Nat)) := by decide

-- mb_false_slot_4_2_1
example : [true, false][1]? = some false ∧ ([91, 5] : List Nat)[1]? = some 5 ∧ ([2, 5] : List Nat)[1]? = some 5 := by decide

-- mb_output_4_3_0
example : mapBitmap [true, false] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = none := by decide

-- mb_output_4_3_1
example : mapBitmap [true, false] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 3] : List Nat),([] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_output_4_3_2
example : mapBitmap [true, false] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 3] : List Nat),([92] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_output_4_3_3
example : mapBitmap [true, false] ([91, 92, 93, 94] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 3] : List Nat),([92, 93, 94] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_success_witness_4_3
example : mapBitmap [true, false] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 3] : List Nat),[],([6, 1] : List Nat)) ∧ filterBitmap [true, false] ([91, 3] : List Nat) = some (([91] : List Nat),[]) := by decide

-- mb_more_4_3
example : mapBitmap [true, false] (([91] : List Nat) ++ ([77, 78] : List Nat)) ([8, 3, 6, 1] : List Nat) = some (([91, 3] : List Nat),([77, 78] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_prefix_suffix_4_3
example : mapBitmap [true, false] (([91, 77, 78] : List Nat).take 1) ([8, 3, 6, 1] : List Nat) = some (([91, 3] : List Nat),[],([6, 1] : List Nat)) ∧ mapBitmap [true, false] ([91, 77, 78] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 3] : List Nat),([91, 77, 78] : List Nat).drop 1,([6, 1] : List Nat)) := by decide

-- mb_false_slot_4_3_1
example : [true, false][1]? = some false ∧ ([91, 3] : List Nat)[1]? = some 3 ∧ ([8, 3, 6, 1] : List Nat)[1]? = some 3 := by decide

-- mb_output_5_0_0
example : mapBitmap [false, true] ([] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_5_0_1
example : mapBitmap [false, true] ([91] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_5_0_2
example : mapBitmap [false, true] ([91, 92] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_5_0_3
example : mapBitmap [false, true] ([91, 92, 93, 94] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_5_1_0
example : mapBitmap [false, true] ([] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_5_1_1
example : mapBitmap [false, true] ([91] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_5_1_2
example : mapBitmap [false, true] ([91, 92] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_5_1_3
example : mapBitmap [false, true] ([91, 92, 93, 94] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_5_2_0
example : mapBitmap [false, true] ([] : List Nat) ([2, 5] : List Nat) = none := by decide

-- mb_output_5_2_1
example : mapBitmap [false, true] ([91] : List Nat) ([2, 5] : List Nat) = some (([2, 91] : List Nat),([] : List Nat),([] : List Nat)) := by decide

-- mb_output_5_2_2
example : mapBitmap [false, true] ([91, 92] : List Nat) ([2, 5] : List Nat) = some (([2, 91] : List Nat),([92] : List Nat),([] : List Nat)) := by decide

-- mb_output_5_2_3
example : mapBitmap [false, true] ([91, 92, 93, 94] : List Nat) ([2, 5] : List Nat) = some (([2, 91] : List Nat),([92, 93, 94] : List Nat),([] : List Nat)) := by decide

-- mb_success_witness_5_2
example : mapBitmap [false, true] ([91] : List Nat) ([2, 5] : List Nat) = some (([2, 91] : List Nat),[],([] : List Nat)) ∧ filterBitmap [false, true] ([2, 91] : List Nat) = some (([91] : List Nat),[]) := by decide

-- mb_more_5_2
example : mapBitmap [false, true] (([91] : List Nat) ++ ([77, 78] : List Nat)) ([2, 5] : List Nat) = some (([2, 91] : List Nat),([77, 78] : List Nat),([] : List Nat)) := by decide

-- mb_prefix_suffix_5_2
example : mapBitmap [false, true] (([91, 77, 78] : List Nat).take 1) ([2, 5] : List Nat) = some (([2, 91] : List Nat),[],([] : List Nat)) ∧ mapBitmap [false, true] ([91, 77, 78] : List Nat) ([2, 5] : List Nat) = some (([2, 91] : List Nat),([91, 77, 78] : List Nat).drop 1,([] : List Nat)) := by decide

-- mb_false_slot_5_2_0
example : [false, true][0]? = some false ∧ ([2, 91] : List Nat)[0]? = some 2 ∧ ([2, 5] : List Nat)[0]? = some 2 := by decide

-- mb_output_5_3_0
example : mapBitmap [false, true] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = none := by decide

-- mb_output_5_3_1
example : mapBitmap [false, true] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 91] : List Nat),([] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_output_5_3_2
example : mapBitmap [false, true] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 91] : List Nat),([92] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_output_5_3_3
example : mapBitmap [false, true] ([91, 92, 93, 94] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 91] : List Nat),([92, 93, 94] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_success_witness_5_3
example : mapBitmap [false, true] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 91] : List Nat),[],([6, 1] : List Nat)) ∧ filterBitmap [false, true] ([8, 91] : List Nat) = some (([91] : List Nat),[]) := by decide

-- mb_more_5_3
example : mapBitmap [false, true] (([91] : List Nat) ++ ([77, 78] : List Nat)) ([8, 3, 6, 1] : List Nat) = some (([8, 91] : List Nat),([77, 78] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_prefix_suffix_5_3
example : mapBitmap [false, true] (([91, 77, 78] : List Nat).take 1) ([8, 3, 6, 1] : List Nat) = some (([8, 91] : List Nat),[],([6, 1] : List Nat)) ∧ mapBitmap [false, true] ([91, 77, 78] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([8, 91] : List Nat),([91, 77, 78] : List Nat).drop 1,([6, 1] : List Nat)) := by decide

-- mb_false_slot_5_3_0
example : [false, true][0]? = some false ∧ ([8, 91] : List Nat)[0]? = some 8 ∧ ([8, 3, 6, 1] : List Nat)[0]? = some 8 := by decide

-- mb_output_6_0_0
example : mapBitmap [true, true] ([] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_6_0_1
example : mapBitmap [true, true] ([91] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_6_0_2
example : mapBitmap [true, true] ([91, 92] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_6_0_3
example : mapBitmap [true, true] ([91, 92, 93, 94] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_6_1_0
example : mapBitmap [true, true] ([] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_6_1_1
example : mapBitmap [true, true] ([91] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_6_1_2
example : mapBitmap [true, true] ([91, 92] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_6_1_3
example : mapBitmap [true, true] ([91, 92, 93, 94] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_6_2_0
example : mapBitmap [true, true] ([] : List Nat) ([2, 5] : List Nat) = none := by decide

-- mb_output_6_2_1
example : mapBitmap [true, true] ([91] : List Nat) ([2, 5] : List Nat) = none := by decide

-- mb_output_6_2_2
example : mapBitmap [true, true] ([91, 92] : List Nat) ([2, 5] : List Nat) = some (([91, 92] : List Nat),([] : List Nat),([] : List Nat)) := by decide

-- mb_output_6_2_3
example : mapBitmap [true, true] ([91, 92, 93, 94] : List Nat) ([2, 5] : List Nat) = some (([91, 92] : List Nat),([93, 94] : List Nat),([] : List Nat)) := by decide

-- mb_success_witness_6_2
example : mapBitmap [true, true] ([91, 92] : List Nat) ([2, 5] : List Nat) = some (([91, 92] : List Nat),[],([] : List Nat)) ∧ filterBitmap [true, true] ([91, 92] : List Nat) = some (([91, 92] : List Nat),[]) := by decide

-- mb_more_6_2
example : mapBitmap [true, true] (([91, 92] : List Nat) ++ ([77, 78] : List Nat)) ([2, 5] : List Nat) = some (([91, 92] : List Nat),([77, 78] : List Nat),([] : List Nat)) := by decide

-- mb_prefix_suffix_6_2
example : mapBitmap [true, true] (([91, 92, 77, 78] : List Nat).take 2) ([2, 5] : List Nat) = some (([91, 92] : List Nat),[],([] : List Nat)) ∧ mapBitmap [true, true] ([91, 92, 77, 78] : List Nat) ([2, 5] : List Nat) = some (([91, 92] : List Nat),([91, 92, 77, 78] : List Nat).drop 2,([] : List Nat)) := by decide

-- mb_output_6_3_0
example : mapBitmap [true, true] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = none := by decide

-- mb_output_6_3_1
example : mapBitmap [true, true] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = none := by decide

-- mb_output_6_3_2
example : mapBitmap [true, true] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 92] : List Nat),([] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_output_6_3_3
example : mapBitmap [true, true] ([91, 92, 93, 94] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 92] : List Nat),([93, 94] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_success_witness_6_3
example : mapBitmap [true, true] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 92] : List Nat),[],([6, 1] : List Nat)) ∧ filterBitmap [true, true] ([91, 92] : List Nat) = some (([91, 92] : List Nat),[]) := by decide

-- mb_more_6_3
example : mapBitmap [true, true] (([91, 92] : List Nat) ++ ([77, 78] : List Nat)) ([8, 3, 6, 1] : List Nat) = some (([91, 92] : List Nat),([77, 78] : List Nat),([6, 1] : List Nat)) := by decide

-- mb_prefix_suffix_6_3
example : mapBitmap [true, true] (([91, 92, 77, 78] : List Nat).take 2) ([8, 3, 6, 1] : List Nat) = some (([91, 92] : List Nat),[],([6, 1] : List Nat)) ∧ mapBitmap [true, true] ([91, 92, 77, 78] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 92] : List Nat),([91, 92, 77, 78] : List Nat).drop 2,([6, 1] : List Nat)) := by decide

-- mb_output_7_0_0
example : mapBitmap [true, false, true] ([] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_7_0_1
example : mapBitmap [true, false, true] ([91] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_7_0_2
example : mapBitmap [true, false, true] ([91, 92] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_7_0_3
example : mapBitmap [true, false, true] ([91, 92, 93, 94] : List Nat) ([] : List Nat) = none := by decide

-- mb_output_7_1_0
example : mapBitmap [true, false, true] ([] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_7_1_1
example : mapBitmap [true, false, true] ([91] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_7_1_2
example : mapBitmap [true, false, true] ([91, 92] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_7_1_3
example : mapBitmap [true, false, true] ([91, 92, 93, 94] : List Nat) ([3] : List Nat) = none := by decide

-- mb_output_7_2_0
example : mapBitmap [true, false, true] ([] : List Nat) ([2, 5] : List Nat) = none := by decide

-- mb_output_7_2_1
example : mapBitmap [true, false, true] ([91] : List Nat) ([2, 5] : List Nat) = none := by decide

-- mb_output_7_2_2
example : mapBitmap [true, false, true] ([91, 92] : List Nat) ([2, 5] : List Nat) = none := by decide

-- mb_output_7_2_3
example : mapBitmap [true, false, true] ([91, 92, 93, 94] : List Nat) ([2, 5] : List Nat) = none := by decide

-- mb_output_7_3_0
example : mapBitmap [true, false, true] ([] : List Nat) ([8, 3, 6, 1] : List Nat) = none := by decide

-- mb_output_7_3_1
example : mapBitmap [true, false, true] ([91] : List Nat) ([8, 3, 6, 1] : List Nat) = none := by decide

-- mb_output_7_3_2
example : mapBitmap [true, false, true] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 3, 92] : List Nat),([] : List Nat),([1] : List Nat)) := by decide

-- mb_output_7_3_3
example : mapBitmap [true, false, true] ([91, 92, 93, 94] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 3, 92] : List Nat),([93, 94] : List Nat),([1] : List Nat)) := by decide

-- mb_success_witness_7_3
example : mapBitmap [true, false, true] ([91, 92] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 3, 92] : List Nat),[],([1] : List Nat)) ∧ filterBitmap [true, false, true] ([91, 3, 92] : List Nat) = some (([91, 92] : List Nat),[]) := by decide

-- mb_more_7_3
example : mapBitmap [true, false, true] (([91, 92] : List Nat) ++ ([77, 78] : List Nat)) ([8, 3, 6, 1] : List Nat) = some (([91, 3, 92] : List Nat),([77, 78] : List Nat),([1] : List Nat)) := by decide

-- mb_prefix_suffix_7_3
example : mapBitmap [true, false, true] (([91, 92, 77, 78] : List Nat).take 2) ([8, 3, 6, 1] : List Nat) = some (([91, 3, 92] : List Nat),[],([1] : List Nat)) ∧ mapBitmap [true, false, true] ([91, 92, 77, 78] : List Nat) ([8, 3, 6, 1] : List Nat) = some (([91, 3, 92] : List Nat),([91, 92, 77, 78] : List Nat).drop 2,([1] : List Nat)) := by decide

-- mb_false_slot_7_3_1
example : [true, false, true][1]? = some false ∧ ([91, 3, 92] : List Nat)[1]? = some 3 ∧ ([8, 3, 6, 1] : List Nat)[1]? = some 3 := by decide


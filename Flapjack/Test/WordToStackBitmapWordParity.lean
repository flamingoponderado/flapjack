import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapWordLemmas
open Flapjack.Compiler.Backend.WordToStack

-- bw_max_0_0
example : ((List.range 0).map (fun x => 2 * x)).foldl max 0 = 0 := maxListGenlistEvens 0

-- bw_max_1_0
example : ((List.range 0).map (fun x => 2 * (x + 1))).foldl max 0 = 0 := maxListGenlistEvens2 0

-- bw_max_0_1
example : ((List.range 1).map (fun x => 2 * x)).foldl max 0 = 0 := maxListGenlistEvens 1

-- bw_max_1_1
example : ((List.range 1).map (fun x => 2 * (x + 1))).foldl max 0 = 2 := maxListGenlistEvens2 1

-- bw_max_0_2
example : ((List.range 2).map (fun x => 2 * x)).foldl max 0 = 2 := maxListGenlistEvens 2

-- bw_max_1_2
example : ((List.range 2).map (fun x => 2 * (x + 1))).foldl max 0 = 4 := maxListGenlistEvens2 2

-- bw_max_0_3
example : ((List.range 3).map (fun x => 2 * x)).foldl max 0 = 4 := maxListGenlistEvens 3

-- bw_max_1_3
example : ((List.range 3).map (fun x => 2 * (x + 1))).foldl max 0 = 6 := maxListGenlistEvens2 3

-- bw_max_0_10
example : ((List.range 10).map (fun x => 2 * x)).foldl max 0 = 18 := maxListGenlistEvens 10

-- bw_max_1_10
example : ((List.range 10).map (fun x => 2 * (x + 1))).foldl max 0 = 20 := maxListGenlistEvens2 10

-- bw_max_0_64
example : ((List.range 64).map (fun x => 2 * x)).foldl max 0 = 126 := maxListGenlistEvens 64

-- bw_max_1_64
example : ((List.range 64).map (fun x => 2 * (x + 1))).foldl max 0 = 128 := maxListGenlistEvens2 64

-- bw_max_0_100
example : ((List.range 100).map (fun x => 2 * x)).foldl max 0 = 198 := maxListGenlistEvens 100

-- bw_max_1_100
example : ((List.range 100).map (fun x => 2 * (x + 1))).foldl max 0 = 200 := maxListGenlistEvens2 100

-- bw_or_value_0_0_1
example : (((0:BitVec 1) ||| 0).toNat) = 0 := by decide

-- bw_or_law_0_0_1
example : (0:BitVec 1) ||| 0 = 0 ↔ (0:BitVec 1) = 0 ∧ (0:BitVec 1) = 0 := wordOrEqZero _ _

-- bw_or_value_0_1_1
example : (((0:BitVec 1) ||| 1).toNat) = 1 := by decide

-- bw_or_law_0_1_1
example : (0:BitVec 1) ||| 1 = 0 ↔ (0:BitVec 1) = 0 ∧ (1:BitVec 1) = 0 := wordOrEqZero _ _

-- bw_orone_0_1
example : ((0:BitVec 1) <<< 1) ||| 1 = ((0:BitVec 1) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_0_1
example : (((0:BitVec 1) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_shift_law_0_1
example : ((0:BitVec 1) <<< 1) >>> 1 = 0 := shiftShiftLemma _ (by decide)

-- bw_or_value_1_0_1
example : (((1:BitVec 1) ||| 0).toNat) = 1 := by decide

-- bw_or_law_1_0_1
example : (1:BitVec 1) ||| 0 = 0 ↔ (1:BitVec 1) = 0 ∧ (0:BitVec 1) = 0 := wordOrEqZero _ _

-- bw_or_value_1_1_1
example : (((1:BitVec 1) ||| 1).toNat) = 1 := by decide

-- bw_or_law_1_1_1
example : (1:BitVec 1) ||| 1 = 0 ↔ (1:BitVec 1) = 0 ∧ (1:BitVec 1) = 0 := wordOrEqZero _ _

-- bw_orone_1_1
example : ((1:BitVec 1) <<< 1) ||| 1 = ((1:BitVec 1) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_1_1
example : (((1:BitVec 1) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_msb_drop_1_1
example : (1:BitVec 1).msb = true ∧ (((1:BitVec 1) <<< 1) >>> 1) ≠ 1 := by decide

-- bw_or_value_0_0_2
example : (((0:BitVec 2) ||| 0).toNat) = 0 := by decide

-- bw_or_law_0_0_2
example : (0:BitVec 2) ||| 0 = 0 ↔ (0:BitVec 2) = 0 ∧ (0:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_0_1_2
example : (((0:BitVec 2) ||| 1).toNat) = 1 := by decide

-- bw_or_law_0_1_2
example : (0:BitVec 2) ||| 1 = 0 ↔ (0:BitVec 2) = 0 ∧ (1:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_0_2_2
example : (((0:BitVec 2) ||| 2).toNat) = 2 := by decide

-- bw_or_law_0_2_2
example : (0:BitVec 2) ||| 2 = 0 ↔ (0:BitVec 2) = 0 ∧ (2:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_0_3_2
example : (((0:BitVec 2) ||| 3).toNat) = 3 := by decide

-- bw_or_law_0_3_2
example : (0:BitVec 2) ||| 3 = 0 ↔ (0:BitVec 2) = 0 ∧ (3:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_orone_0_2
example : ((0:BitVec 2) <<< 1) ||| 1 = ((0:BitVec 2) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_0_2
example : (((0:BitVec 2) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_shift_law_0_2
example : ((0:BitVec 2) <<< 1) >>> 1 = 0 := shiftShiftLemma _ (by decide)

-- bw_or_value_1_0_2
example : (((1:BitVec 2) ||| 0).toNat) = 1 := by decide

-- bw_or_law_1_0_2
example : (1:BitVec 2) ||| 0 = 0 ↔ (1:BitVec 2) = 0 ∧ (0:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_1_1_2
example : (((1:BitVec 2) ||| 1).toNat) = 1 := by decide

-- bw_or_law_1_1_2
example : (1:BitVec 2) ||| 1 = 0 ↔ (1:BitVec 2) = 0 ∧ (1:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_1_2_2
example : (((1:BitVec 2) ||| 2).toNat) = 3 := by decide

-- bw_or_law_1_2_2
example : (1:BitVec 2) ||| 2 = 0 ↔ (1:BitVec 2) = 0 ∧ (2:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_1_3_2
example : (((1:BitVec 2) ||| 3).toNat) = 3 := by decide

-- bw_or_law_1_3_2
example : (1:BitVec 2) ||| 3 = 0 ↔ (1:BitVec 2) = 0 ∧ (3:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_orone_1_2
example : ((1:BitVec 2) <<< 1) ||| 1 = ((1:BitVec 2) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_1_2
example : (((1:BitVec 2) <<< 1) >>> 1).toNat = 1 := by decide

-- bw_shift_law_1_2
example : ((1:BitVec 2) <<< 1) >>> 1 = 1 := shiftShiftLemma _ (by decide)

-- bw_or_value_2_0_2
example : (((2:BitVec 2) ||| 0).toNat) = 2 := by decide

-- bw_or_law_2_0_2
example : (2:BitVec 2) ||| 0 = 0 ↔ (2:BitVec 2) = 0 ∧ (0:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_2_1_2
example : (((2:BitVec 2) ||| 1).toNat) = 3 := by decide

-- bw_or_law_2_1_2
example : (2:BitVec 2) ||| 1 = 0 ↔ (2:BitVec 2) = 0 ∧ (1:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_2_2_2
example : (((2:BitVec 2) ||| 2).toNat) = 2 := by decide

-- bw_or_law_2_2_2
example : (2:BitVec 2) ||| 2 = 0 ↔ (2:BitVec 2) = 0 ∧ (2:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_2_3_2
example : (((2:BitVec 2) ||| 3).toNat) = 3 := by decide

-- bw_or_law_2_3_2
example : (2:BitVec 2) ||| 3 = 0 ↔ (2:BitVec 2) = 0 ∧ (3:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_orone_2_2
example : ((2:BitVec 2) <<< 1) ||| 1 = ((2:BitVec 2) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_2_2
example : (((2:BitVec 2) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_msb_drop_2_2
example : (2:BitVec 2).msb = true ∧ (((2:BitVec 2) <<< 1) >>> 1) ≠ 2 := by decide

-- bw_or_value_3_0_2
example : (((3:BitVec 2) ||| 0).toNat) = 3 := by decide

-- bw_or_law_3_0_2
example : (3:BitVec 2) ||| 0 = 0 ↔ (3:BitVec 2) = 0 ∧ (0:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_3_1_2
example : (((3:BitVec 2) ||| 1).toNat) = 3 := by decide

-- bw_or_law_3_1_2
example : (3:BitVec 2) ||| 1 = 0 ↔ (3:BitVec 2) = 0 ∧ (1:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_3_2_2
example : (((3:BitVec 2) ||| 2).toNat) = 3 := by decide

-- bw_or_law_3_2_2
example : (3:BitVec 2) ||| 2 = 0 ↔ (3:BitVec 2) = 0 ∧ (2:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_or_value_3_3_2
example : (((3:BitVec 2) ||| 3).toNat) = 3 := by decide

-- bw_or_law_3_3_2
example : (3:BitVec 2) ||| 3 = 0 ↔ (3:BitVec 2) = 0 ∧ (3:BitVec 2) = 0 := wordOrEqZero _ _

-- bw_orone_3_2
example : ((3:BitVec 2) <<< 1) ||| 1 = ((3:BitVec 2) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_3_2
example : (((3:BitVec 2) <<< 1) >>> 1).toNat = 1 := by decide

-- bw_msb_drop_3_2
example : (3:BitVec 2).msb = true ∧ (((3:BitVec 2) <<< 1) >>> 1) ≠ 3 := by decide

-- bw_or_value_0_0_32
example : (((0:BitVec 32) ||| 0).toNat) = 0 := by decide

-- bw_or_law_0_0_32
example : (0:BitVec 32) ||| 0 = 0 ↔ (0:BitVec 32) = 0 ∧ (0:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_0_1_32
example : (((0:BitVec 32) ||| 1).toNat) = 1 := by decide

-- bw_or_law_0_1_32
example : (0:BitVec 32) ||| 1 = 0 ↔ (0:BitVec 32) = 0 ∧ (1:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_0_2_32
example : (((0:BitVec 32) ||| 2147483647).toNat) = 2147483647 := by decide

-- bw_or_law_0_2_32
example : (0:BitVec 32) ||| 2147483647 = 0 ↔ (0:BitVec 32) = 0 ∧ (2147483647:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_0_3_32
example : (((0:BitVec 32) ||| 2147483648).toNat) = 2147483648 := by decide

-- bw_or_law_0_3_32
example : (0:BitVec 32) ||| 2147483648 = 0 ↔ (0:BitVec 32) = 0 ∧ (2147483648:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_0_4_32
example : (((0:BitVec 32) ||| 4294967295).toNat) = 4294967295 := by decide

-- bw_or_law_0_4_32
example : (0:BitVec 32) ||| 4294967295 = 0 ↔ (0:BitVec 32) = 0 ∧ (4294967295:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_orone_0_32
example : ((0:BitVec 32) <<< 1) ||| 1 = ((0:BitVec 32) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_0_32
example : (((0:BitVec 32) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_shift_law_0_32
example : ((0:BitVec 32) <<< 1) >>> 1 = 0 := shiftShiftLemma _ (by decide)

-- bw_or_value_1_0_32
example : (((1:BitVec 32) ||| 0).toNat) = 1 := by decide

-- bw_or_law_1_0_32
example : (1:BitVec 32) ||| 0 = 0 ↔ (1:BitVec 32) = 0 ∧ (0:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_1_1_32
example : (((1:BitVec 32) ||| 1).toNat) = 1 := by decide

-- bw_or_law_1_1_32
example : (1:BitVec 32) ||| 1 = 0 ↔ (1:BitVec 32) = 0 ∧ (1:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_1_2_32
example : (((1:BitVec 32) ||| 2147483647).toNat) = 2147483647 := by decide

-- bw_or_law_1_2_32
example : (1:BitVec 32) ||| 2147483647 = 0 ↔ (1:BitVec 32) = 0 ∧ (2147483647:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_1_3_32
example : (((1:BitVec 32) ||| 2147483648).toNat) = 2147483649 := by decide

-- bw_or_law_1_3_32
example : (1:BitVec 32) ||| 2147483648 = 0 ↔ (1:BitVec 32) = 0 ∧ (2147483648:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_1_4_32
example : (((1:BitVec 32) ||| 4294967295).toNat) = 4294967295 := by decide

-- bw_or_law_1_4_32
example : (1:BitVec 32) ||| 4294967295 = 0 ↔ (1:BitVec 32) = 0 ∧ (4294967295:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_orone_1_32
example : ((1:BitVec 32) <<< 1) ||| 1 = ((1:BitVec 32) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_1_32
example : (((1:BitVec 32) <<< 1) >>> 1).toNat = 1 := by decide

-- bw_shift_law_1_32
example : ((1:BitVec 32) <<< 1) >>> 1 = 1 := shiftShiftLemma _ (by decide)

-- bw_or_value_2_0_32
example : (((2147483647:BitVec 32) ||| 0).toNat) = 2147483647 := by decide

-- bw_or_law_2_0_32
example : (2147483647:BitVec 32) ||| 0 = 0 ↔ (2147483647:BitVec 32) = 0 ∧ (0:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_2_1_32
example : (((2147483647:BitVec 32) ||| 1).toNat) = 2147483647 := by decide

-- bw_or_law_2_1_32
example : (2147483647:BitVec 32) ||| 1 = 0 ↔ (2147483647:BitVec 32) = 0 ∧ (1:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_2_2_32
example : (((2147483647:BitVec 32) ||| 2147483647).toNat) = 2147483647 := by decide

-- bw_or_law_2_2_32
example : (2147483647:BitVec 32) ||| 2147483647 = 0 ↔ (2147483647:BitVec 32) = 0 ∧ (2147483647:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_2_3_32
example : (((2147483647:BitVec 32) ||| 2147483648).toNat) = 4294967295 := by decide

-- bw_or_law_2_3_32
example : (2147483647:BitVec 32) ||| 2147483648 = 0 ↔ (2147483647:BitVec 32) = 0 ∧ (2147483648:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_2_4_32
example : (((2147483647:BitVec 32) ||| 4294967295).toNat) = 4294967295 := by decide

-- bw_or_law_2_4_32
example : (2147483647:BitVec 32) ||| 4294967295 = 0 ↔ (2147483647:BitVec 32) = 0 ∧ (4294967295:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_orone_2_32
example : ((2147483647:BitVec 32) <<< 1) ||| 1 = ((2147483647:BitVec 32) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_2_32
example : (((2147483647:BitVec 32) <<< 1) >>> 1).toNat = 2147483647 := by decide

-- bw_shift_law_2_32
example : ((2147483647:BitVec 32) <<< 1) >>> 1 = 2147483647 := shiftShiftLemma _ (by decide)

-- bw_or_value_3_0_32
example : (((2147483648:BitVec 32) ||| 0).toNat) = 2147483648 := by decide

-- bw_or_law_3_0_32
example : (2147483648:BitVec 32) ||| 0 = 0 ↔ (2147483648:BitVec 32) = 0 ∧ (0:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_3_1_32
example : (((2147483648:BitVec 32) ||| 1).toNat) = 2147483649 := by decide

-- bw_or_law_3_1_32
example : (2147483648:BitVec 32) ||| 1 = 0 ↔ (2147483648:BitVec 32) = 0 ∧ (1:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_3_2_32
example : (((2147483648:BitVec 32) ||| 2147483647).toNat) = 4294967295 := by decide

-- bw_or_law_3_2_32
example : (2147483648:BitVec 32) ||| 2147483647 = 0 ↔ (2147483648:BitVec 32) = 0 ∧ (2147483647:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_3_3_32
example : (((2147483648:BitVec 32) ||| 2147483648).toNat) = 2147483648 := by decide

-- bw_or_law_3_3_32
example : (2147483648:BitVec 32) ||| 2147483648 = 0 ↔ (2147483648:BitVec 32) = 0 ∧ (2147483648:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_3_4_32
example : (((2147483648:BitVec 32) ||| 4294967295).toNat) = 4294967295 := by decide

-- bw_or_law_3_4_32
example : (2147483648:BitVec 32) ||| 4294967295 = 0 ↔ (2147483648:BitVec 32) = 0 ∧ (4294967295:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_orone_3_32
example : ((2147483648:BitVec 32) <<< 1) ||| 1 = ((2147483648:BitVec 32) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_3_32
example : (((2147483648:BitVec 32) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_msb_drop_3_32
example : (2147483648:BitVec 32).msb = true ∧ (((2147483648:BitVec 32) <<< 1) >>> 1) ≠ 2147483648 := by decide

-- bw_or_value_4_0_32
example : (((4294967295:BitVec 32) ||| 0).toNat) = 4294967295 := by decide

-- bw_or_law_4_0_32
example : (4294967295:BitVec 32) ||| 0 = 0 ↔ (4294967295:BitVec 32) = 0 ∧ (0:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_4_1_32
example : (((4294967295:BitVec 32) ||| 1).toNat) = 4294967295 := by decide

-- bw_or_law_4_1_32
example : (4294967295:BitVec 32) ||| 1 = 0 ↔ (4294967295:BitVec 32) = 0 ∧ (1:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_4_2_32
example : (((4294967295:BitVec 32) ||| 2147483647).toNat) = 4294967295 := by decide

-- bw_or_law_4_2_32
example : (4294967295:BitVec 32) ||| 2147483647 = 0 ↔ (4294967295:BitVec 32) = 0 ∧ (2147483647:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_4_3_32
example : (((4294967295:BitVec 32) ||| 2147483648).toNat) = 4294967295 := by decide

-- bw_or_law_4_3_32
example : (4294967295:BitVec 32) ||| 2147483648 = 0 ↔ (4294967295:BitVec 32) = 0 ∧ (2147483648:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_or_value_4_4_32
example : (((4294967295:BitVec 32) ||| 4294967295).toNat) = 4294967295 := by decide

-- bw_or_law_4_4_32
example : (4294967295:BitVec 32) ||| 4294967295 = 0 ↔ (4294967295:BitVec 32) = 0 ∧ (4294967295:BitVec 32) = 0 := wordOrEqZero _ _

-- bw_orone_4_32
example : ((4294967295:BitVec 32) <<< 1) ||| 1 = ((4294967295:BitVec 32) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_4_32
example : (((4294967295:BitVec 32) <<< 1) >>> 1).toNat = 2147483647 := by decide

-- bw_msb_drop_4_32
example : (4294967295:BitVec 32).msb = true ∧ (((4294967295:BitVec 32) <<< 1) >>> 1) ≠ 4294967295 := by decide

-- bw_or_value_0_0_64
example : (((0:BitVec 64) ||| 0).toNat) = 0 := by decide

-- bw_or_law_0_0_64
example : (0:BitVec 64) ||| 0 = 0 ↔ (0:BitVec 64) = 0 ∧ (0:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_0_1_64
example : (((0:BitVec 64) ||| 1).toNat) = 1 := by decide

-- bw_or_law_0_1_64
example : (0:BitVec 64) ||| 1 = 0 ↔ (0:BitVec 64) = 0 ∧ (1:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_0_2_64
example : (((0:BitVec 64) ||| 9223372036854775807).toNat) = 9223372036854775807 := by decide

-- bw_or_law_0_2_64
example : (0:BitVec 64) ||| 9223372036854775807 = 0 ↔ (0:BitVec 64) = 0 ∧ (9223372036854775807:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_0_3_64
example : (((0:BitVec 64) ||| 9223372036854775808).toNat) = 9223372036854775808 := by decide

-- bw_or_law_0_3_64
example : (0:BitVec 64) ||| 9223372036854775808 = 0 ↔ (0:BitVec 64) = 0 ∧ (9223372036854775808:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_0_4_64
example : (((0:BitVec 64) ||| 18446744073709551615).toNat) = 18446744073709551615 := by decide

-- bw_or_law_0_4_64
example : (0:BitVec 64) ||| 18446744073709551615 = 0 ↔ (0:BitVec 64) = 0 ∧ (18446744073709551615:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_orone_0_64
example : ((0:BitVec 64) <<< 1) ||| 1 = ((0:BitVec 64) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_0_64
example : (((0:BitVec 64) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_shift_law_0_64
example : ((0:BitVec 64) <<< 1) >>> 1 = 0 := shiftShiftLemma _ (by decide)

-- bw_or_value_1_0_64
example : (((1:BitVec 64) ||| 0).toNat) = 1 := by decide

-- bw_or_law_1_0_64
example : (1:BitVec 64) ||| 0 = 0 ↔ (1:BitVec 64) = 0 ∧ (0:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_1_1_64
example : (((1:BitVec 64) ||| 1).toNat) = 1 := by decide

-- bw_or_law_1_1_64
example : (1:BitVec 64) ||| 1 = 0 ↔ (1:BitVec 64) = 0 ∧ (1:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_1_2_64
example : (((1:BitVec 64) ||| 9223372036854775807).toNat) = 9223372036854775807 := by decide

-- bw_or_law_1_2_64
example : (1:BitVec 64) ||| 9223372036854775807 = 0 ↔ (1:BitVec 64) = 0 ∧ (9223372036854775807:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_1_3_64
example : (((1:BitVec 64) ||| 9223372036854775808).toNat) = 9223372036854775809 := by decide

-- bw_or_law_1_3_64
example : (1:BitVec 64) ||| 9223372036854775808 = 0 ↔ (1:BitVec 64) = 0 ∧ (9223372036854775808:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_1_4_64
example : (((1:BitVec 64) ||| 18446744073709551615).toNat) = 18446744073709551615 := by decide

-- bw_or_law_1_4_64
example : (1:BitVec 64) ||| 18446744073709551615 = 0 ↔ (1:BitVec 64) = 0 ∧ (18446744073709551615:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_orone_1_64
example : ((1:BitVec 64) <<< 1) ||| 1 = ((1:BitVec 64) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_1_64
example : (((1:BitVec 64) <<< 1) >>> 1).toNat = 1 := by decide

-- bw_shift_law_1_64
example : ((1:BitVec 64) <<< 1) >>> 1 = 1 := shiftShiftLemma _ (by decide)

-- bw_or_value_2_0_64
example : (((9223372036854775807:BitVec 64) ||| 0).toNat) = 9223372036854775807 := by decide

-- bw_or_law_2_0_64
example : (9223372036854775807:BitVec 64) ||| 0 = 0 ↔ (9223372036854775807:BitVec 64) = 0 ∧ (0:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_2_1_64
example : (((9223372036854775807:BitVec 64) ||| 1).toNat) = 9223372036854775807 := by decide

-- bw_or_law_2_1_64
example : (9223372036854775807:BitVec 64) ||| 1 = 0 ↔ (9223372036854775807:BitVec 64) = 0 ∧ (1:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_2_2_64
example : (((9223372036854775807:BitVec 64) ||| 9223372036854775807).toNat) = 9223372036854775807 := by decide

-- bw_or_law_2_2_64
example : (9223372036854775807:BitVec 64) ||| 9223372036854775807 = 0 ↔ (9223372036854775807:BitVec 64) = 0 ∧ (9223372036854775807:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_2_3_64
example : (((9223372036854775807:BitVec 64) ||| 9223372036854775808).toNat) = 18446744073709551615 := by decide

-- bw_or_law_2_3_64
example : (9223372036854775807:BitVec 64) ||| 9223372036854775808 = 0 ↔ (9223372036854775807:BitVec 64) = 0 ∧ (9223372036854775808:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_2_4_64
example : (((9223372036854775807:BitVec 64) ||| 18446744073709551615).toNat) = 18446744073709551615 := by decide

-- bw_or_law_2_4_64
example : (9223372036854775807:BitVec 64) ||| 18446744073709551615 = 0 ↔ (9223372036854775807:BitVec 64) = 0 ∧ (18446744073709551615:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_orone_2_64
example : ((9223372036854775807:BitVec 64) <<< 1) ||| 1 = ((9223372036854775807:BitVec 64) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_2_64
example : (((9223372036854775807:BitVec 64) <<< 1) >>> 1).toNat = 9223372036854775807 := by decide

-- bw_shift_law_2_64
example : ((9223372036854775807:BitVec 64) <<< 1) >>> 1 = 9223372036854775807 := shiftShiftLemma _ (by decide)

-- bw_or_value_3_0_64
example : (((9223372036854775808:BitVec 64) ||| 0).toNat) = 9223372036854775808 := by decide

-- bw_or_law_3_0_64
example : (9223372036854775808:BitVec 64) ||| 0 = 0 ↔ (9223372036854775808:BitVec 64) = 0 ∧ (0:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_3_1_64
example : (((9223372036854775808:BitVec 64) ||| 1).toNat) = 9223372036854775809 := by decide

-- bw_or_law_3_1_64
example : (9223372036854775808:BitVec 64) ||| 1 = 0 ↔ (9223372036854775808:BitVec 64) = 0 ∧ (1:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_3_2_64
example : (((9223372036854775808:BitVec 64) ||| 9223372036854775807).toNat) = 18446744073709551615 := by decide

-- bw_or_law_3_2_64
example : (9223372036854775808:BitVec 64) ||| 9223372036854775807 = 0 ↔ (9223372036854775808:BitVec 64) = 0 ∧ (9223372036854775807:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_3_3_64
example : (((9223372036854775808:BitVec 64) ||| 9223372036854775808).toNat) = 9223372036854775808 := by decide

-- bw_or_law_3_3_64
example : (9223372036854775808:BitVec 64) ||| 9223372036854775808 = 0 ↔ (9223372036854775808:BitVec 64) = 0 ∧ (9223372036854775808:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_3_4_64
example : (((9223372036854775808:BitVec 64) ||| 18446744073709551615).toNat) = 18446744073709551615 := by decide

-- bw_or_law_3_4_64
example : (9223372036854775808:BitVec 64) ||| 18446744073709551615 = 0 ↔ (9223372036854775808:BitVec 64) = 0 ∧ (18446744073709551615:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_orone_3_64
example : ((9223372036854775808:BitVec 64) <<< 1) ||| 1 = ((9223372036854775808:BitVec 64) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_3_64
example : (((9223372036854775808:BitVec 64) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_msb_drop_3_64
example : (9223372036854775808:BitVec 64).msb = true ∧ (((9223372036854775808:BitVec 64) <<< 1) >>> 1) ≠ 9223372036854775808 := by decide

-- bw_or_value_4_0_64
example : (((18446744073709551615:BitVec 64) ||| 0).toNat) = 18446744073709551615 := by decide

-- bw_or_law_4_0_64
example : (18446744073709551615:BitVec 64) ||| 0 = 0 ↔ (18446744073709551615:BitVec 64) = 0 ∧ (0:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_4_1_64
example : (((18446744073709551615:BitVec 64) ||| 1).toNat) = 18446744073709551615 := by decide

-- bw_or_law_4_1_64
example : (18446744073709551615:BitVec 64) ||| 1 = 0 ↔ (18446744073709551615:BitVec 64) = 0 ∧ (1:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_4_2_64
example : (((18446744073709551615:BitVec 64) ||| 9223372036854775807).toNat) = 18446744073709551615 := by decide

-- bw_or_law_4_2_64
example : (18446744073709551615:BitVec 64) ||| 9223372036854775807 = 0 ↔ (18446744073709551615:BitVec 64) = 0 ∧ (9223372036854775807:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_4_3_64
example : (((18446744073709551615:BitVec 64) ||| 9223372036854775808).toNat) = 18446744073709551615 := by decide

-- bw_or_law_4_3_64
example : (18446744073709551615:BitVec 64) ||| 9223372036854775808 = 0 ↔ (18446744073709551615:BitVec 64) = 0 ∧ (9223372036854775808:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_or_value_4_4_64
example : (((18446744073709551615:BitVec 64) ||| 18446744073709551615).toNat) = 18446744073709551615 := by decide

-- bw_or_law_4_4_64
example : (18446744073709551615:BitVec 64) ||| 18446744073709551615 = 0 ↔ (18446744073709551615:BitVec 64) = 0 ∧ (18446744073709551615:BitVec 64) = 0 := wordOrEqZero _ _

-- bw_orone_4_64
example : ((18446744073709551615:BitVec 64) <<< 1) ||| 1 = ((18446744073709551615:BitVec 64) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_4_64
example : (((18446744073709551615:BitVec 64) <<< 1) >>> 1).toNat = 9223372036854775807 := by decide

-- bw_msb_drop_4_64
example : (18446744073709551615:BitVec 64).msb = true ∧ (((18446744073709551615:BitVec 64) <<< 1) >>> 1) ≠ 18446744073709551615 := by decide

-- bw_or_value_0_0_80
example : (((0:BitVec 80) ||| 0).toNat) = 0 := by decide

-- bw_or_law_0_0_80
example : (0:BitVec 80) ||| 0 = 0 ↔ (0:BitVec 80) = 0 ∧ (0:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_0_1_80
example : (((0:BitVec 80) ||| 1).toNat) = 1 := by decide

-- bw_or_law_0_1_80
example : (0:BitVec 80) ||| 1 = 0 ↔ (0:BitVec 80) = 0 ∧ (1:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_0_2_80
example : (((0:BitVec 80) ||| 604462909807314587353087).toNat) = 604462909807314587353087 := by decide

-- bw_or_law_0_2_80
example : (0:BitVec 80) ||| 604462909807314587353087 = 0 ↔ (0:BitVec 80) = 0 ∧ (604462909807314587353087:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_0_3_80
example : (((0:BitVec 80) ||| 604462909807314587353088).toNat) = 604462909807314587353088 := by decide

-- bw_or_law_0_3_80
example : (0:BitVec 80) ||| 604462909807314587353088 = 0 ↔ (0:BitVec 80) = 0 ∧ (604462909807314587353088:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_0_4_80
example : (((0:BitVec 80) ||| 1208925819614629174706175).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_0_4_80
example : (0:BitVec 80) ||| 1208925819614629174706175 = 0 ↔ (0:BitVec 80) = 0 ∧ (1208925819614629174706175:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_orone_0_80
example : ((0:BitVec 80) <<< 1) ||| 1 = ((0:BitVec 80) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_0_80
example : (((0:BitVec 80) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_shift_law_0_80
example : ((0:BitVec 80) <<< 1) >>> 1 = 0 := shiftShiftLemma _ (by decide)

-- bw_or_value_1_0_80
example : (((1:BitVec 80) ||| 0).toNat) = 1 := by decide

-- bw_or_law_1_0_80
example : (1:BitVec 80) ||| 0 = 0 ↔ (1:BitVec 80) = 0 ∧ (0:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_1_1_80
example : (((1:BitVec 80) ||| 1).toNat) = 1 := by decide

-- bw_or_law_1_1_80
example : (1:BitVec 80) ||| 1 = 0 ↔ (1:BitVec 80) = 0 ∧ (1:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_1_2_80
example : (((1:BitVec 80) ||| 604462909807314587353087).toNat) = 604462909807314587353087 := by decide

-- bw_or_law_1_2_80
example : (1:BitVec 80) ||| 604462909807314587353087 = 0 ↔ (1:BitVec 80) = 0 ∧ (604462909807314587353087:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_1_3_80
example : (((1:BitVec 80) ||| 604462909807314587353088).toNat) = 604462909807314587353089 := by decide

-- bw_or_law_1_3_80
example : (1:BitVec 80) ||| 604462909807314587353088 = 0 ↔ (1:BitVec 80) = 0 ∧ (604462909807314587353088:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_1_4_80
example : (((1:BitVec 80) ||| 1208925819614629174706175).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_1_4_80
example : (1:BitVec 80) ||| 1208925819614629174706175 = 0 ↔ (1:BitVec 80) = 0 ∧ (1208925819614629174706175:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_orone_1_80
example : ((1:BitVec 80) <<< 1) ||| 1 = ((1:BitVec 80) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_1_80
example : (((1:BitVec 80) <<< 1) >>> 1).toNat = 1 := by decide

-- bw_shift_law_1_80
example : ((1:BitVec 80) <<< 1) >>> 1 = 1 := shiftShiftLemma _ (by decide)

-- bw_or_value_2_0_80
example : (((604462909807314587353087:BitVec 80) ||| 0).toNat) = 604462909807314587353087 := by decide

-- bw_or_law_2_0_80
example : (604462909807314587353087:BitVec 80) ||| 0 = 0 ↔ (604462909807314587353087:BitVec 80) = 0 ∧ (0:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_2_1_80
example : (((604462909807314587353087:BitVec 80) ||| 1).toNat) = 604462909807314587353087 := by decide

-- bw_or_law_2_1_80
example : (604462909807314587353087:BitVec 80) ||| 1 = 0 ↔ (604462909807314587353087:BitVec 80) = 0 ∧ (1:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_2_2_80
example : (((604462909807314587353087:BitVec 80) ||| 604462909807314587353087).toNat) = 604462909807314587353087 := by decide

-- bw_or_law_2_2_80
example : (604462909807314587353087:BitVec 80) ||| 604462909807314587353087 = 0 ↔ (604462909807314587353087:BitVec 80) = 0 ∧ (604462909807314587353087:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_2_3_80
example : (((604462909807314587353087:BitVec 80) ||| 604462909807314587353088).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_2_3_80
example : (604462909807314587353087:BitVec 80) ||| 604462909807314587353088 = 0 ↔ (604462909807314587353087:BitVec 80) = 0 ∧ (604462909807314587353088:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_2_4_80
example : (((604462909807314587353087:BitVec 80) ||| 1208925819614629174706175).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_2_4_80
example : (604462909807314587353087:BitVec 80) ||| 1208925819614629174706175 = 0 ↔ (604462909807314587353087:BitVec 80) = 0 ∧ (1208925819614629174706175:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_orone_2_80
example : ((604462909807314587353087:BitVec 80) <<< 1) ||| 1 = ((604462909807314587353087:BitVec 80) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_2_80
example : (((604462909807314587353087:BitVec 80) <<< 1) >>> 1).toNat = 604462909807314587353087 := by decide

-- bw_shift_law_2_80
example : ((604462909807314587353087:BitVec 80) <<< 1) >>> 1 = 604462909807314587353087 := shiftShiftLemma _ (by decide)

-- bw_or_value_3_0_80
example : (((604462909807314587353088:BitVec 80) ||| 0).toNat) = 604462909807314587353088 := by decide

-- bw_or_law_3_0_80
example : (604462909807314587353088:BitVec 80) ||| 0 = 0 ↔ (604462909807314587353088:BitVec 80) = 0 ∧ (0:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_3_1_80
example : (((604462909807314587353088:BitVec 80) ||| 1).toNat) = 604462909807314587353089 := by decide

-- bw_or_law_3_1_80
example : (604462909807314587353088:BitVec 80) ||| 1 = 0 ↔ (604462909807314587353088:BitVec 80) = 0 ∧ (1:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_3_2_80
example : (((604462909807314587353088:BitVec 80) ||| 604462909807314587353087).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_3_2_80
example : (604462909807314587353088:BitVec 80) ||| 604462909807314587353087 = 0 ↔ (604462909807314587353088:BitVec 80) = 0 ∧ (604462909807314587353087:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_3_3_80
example : (((604462909807314587353088:BitVec 80) ||| 604462909807314587353088).toNat) = 604462909807314587353088 := by decide

-- bw_or_law_3_3_80
example : (604462909807314587353088:BitVec 80) ||| 604462909807314587353088 = 0 ↔ (604462909807314587353088:BitVec 80) = 0 ∧ (604462909807314587353088:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_3_4_80
example : (((604462909807314587353088:BitVec 80) ||| 1208925819614629174706175).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_3_4_80
example : (604462909807314587353088:BitVec 80) ||| 1208925819614629174706175 = 0 ↔ (604462909807314587353088:BitVec 80) = 0 ∧ (1208925819614629174706175:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_orone_3_80
example : ((604462909807314587353088:BitVec 80) <<< 1) ||| 1 = ((604462909807314587353088:BitVec 80) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_3_80
example : (((604462909807314587353088:BitVec 80) <<< 1) >>> 1).toNat = 0 := by decide

-- bw_msb_drop_3_80
example : (604462909807314587353088:BitVec 80).msb = true ∧ (((604462909807314587353088:BitVec 80) <<< 1) >>> 1) ≠ 604462909807314587353088 := by decide

-- bw_or_value_4_0_80
example : (((1208925819614629174706175:BitVec 80) ||| 0).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_4_0_80
example : (1208925819614629174706175:BitVec 80) ||| 0 = 0 ↔ (1208925819614629174706175:BitVec 80) = 0 ∧ (0:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_4_1_80
example : (((1208925819614629174706175:BitVec 80) ||| 1).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_4_1_80
example : (1208925819614629174706175:BitVec 80) ||| 1 = 0 ↔ (1208925819614629174706175:BitVec 80) = 0 ∧ (1:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_4_2_80
example : (((1208925819614629174706175:BitVec 80) ||| 604462909807314587353087).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_4_2_80
example : (1208925819614629174706175:BitVec 80) ||| 604462909807314587353087 = 0 ↔ (1208925819614629174706175:BitVec 80) = 0 ∧ (604462909807314587353087:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_4_3_80
example : (((1208925819614629174706175:BitVec 80) ||| 604462909807314587353088).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_4_3_80
example : (1208925819614629174706175:BitVec 80) ||| 604462909807314587353088 = 0 ↔ (1208925819614629174706175:BitVec 80) = 0 ∧ (604462909807314587353088:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_or_value_4_4_80
example : (((1208925819614629174706175:BitVec 80) ||| 1208925819614629174706175).toNat) = 1208925819614629174706175 := by decide

-- bw_or_law_4_4_80
example : (1208925819614629174706175:BitVec 80) ||| 1208925819614629174706175 = 0 ↔ (1208925819614629174706175:BitVec 80) = 0 ∧ (1208925819614629174706175:BitVec 80) = 0 := wordOrEqZero _ _

-- bw_orone_4_80
example : ((1208925819614629174706175:BitVec 80) <<< 1) ||| 1 = ((1208925819614629174706175:BitVec 80) <<< 1) + 1 := wordShiftOrOne _

-- bw_shift_value_4_80
example : (((1208925819614629174706175:BitVec 80) <<< 1) >>> 1).toNat = 604462909807314587353087 := by decide

-- bw_msb_drop_4_80
example : (1208925819614629174706175:BitVec 80).msb = true ∧ (((1208925819614629174706175:BitVec 80) <<< 1) >>> 1) ≠ 1208925819614629174706175 := by decide

example {width : Nat} [NeZero width] (n : BitVec width) :
    (n <<< 1) ||| 1 = (n <<< 1) + 1 := wordShiftOrOne n
example (n : Nat) : ((List.range n).map (fun x => 2 * x)).foldl max 0 = 2 * (n - 1) := maxListGenlistEvens n

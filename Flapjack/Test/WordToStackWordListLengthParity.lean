import Flapjack.Compiler.Backend.WordToStack.Proofs.WordListLength
open Flapjack.Compiler.Backend.WordToStack
set_option maxRecDepth 8192

-- wl_length_1_0_0
example : (wordListW (width := 1) [] 0).length = if (0 : Nat) = 0 then 1 else (0 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_0_1
example : (wordListW (width := 1) [] 1).length = if (1 : Nat) = 0 then 1 else (0 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_0_2
example : (wordListW (width := 1) [] 2).length = if (2 : Nat) = 0 then 1 else (0 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_0_7
example : (wordListW (width := 1) [] 7).length = if (7 : Nat) = 0 then 1 else (0 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_0_80
example : (wordListW (width := 1) [] 80).length = if (80 : Nat) = 0 then 1 else (0 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_0_99
example : (wordListW (width := 1) [] 99).length = if (99 : Nat) = 0 then 1 else (0 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_1_0
example : (wordListW (width := 1) [true] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_1_1
example : (wordListW (width := 1) [true] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_1_2
example : (wordListW (width := 1) [true] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_1_7
example : (wordListW (width := 1) [true] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_1_80
example : (wordListW (width := 1) [true] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_1_99
example : (wordListW (width := 1) [true] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_2_0
example : (wordListW (width := 1) [false] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_2_1
example : (wordListW (width := 1) [false] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_2_2
example : (wordListW (width := 1) [false] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_2_7
example : (wordListW (width := 1) [false] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_2_80
example : (wordListW (width := 1) [false] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_2_99
example : (wordListW (width := 1) [false] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_3_0
example : (wordListW (width := 1) [true, false, true] 0).length = if (0 : Nat) = 0 then 1 else (3 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_3_1
example : (wordListW (width := 1) [true, false, true] 1).length = if (1 : Nat) = 0 then 1 else (3 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_3_2
example : (wordListW (width := 1) [true, false, true] 2).length = if (2 : Nat) = 0 then 1 else (3 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_3_7
example : (wordListW (width := 1) [true, false, true] 7).length = if (7 : Nat) = 0 then 1 else (3 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_3_80
example : (wordListW (width := 1) [true, false, true] 80).length = if (80 : Nat) = 0 then 1 else (3 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_3_99
example : (wordListW (width := 1) [true, false, true] 99).length = if (99 : Nat) = 0 then 1 else (3 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_4_0
example : (wordListW (width := 1) [false, false, false, false, false, false, false, false] 0).length = if (0 : Nat) = 0 then 1 else (8 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_4_1
example : (wordListW (width := 1) [false, false, false, false, false, false, false, false] 1).length = if (1 : Nat) = 0 then 1 else (8 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_4_2
example : (wordListW (width := 1) [false, false, false, false, false, false, false, false] 2).length = if (2 : Nat) = 0 then 1 else (8 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_4_7
example : (wordListW (width := 1) [false, false, false, false, false, false, false, false] 7).length = if (7 : Nat) = 0 then 1 else (8 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_4_80
example : (wordListW (width := 1) [false, false, false, false, false, false, false, false] 80).length = if (80 : Nat) = 0 then 1 else (8 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_4_99
example : (wordListW (width := 1) [false, false, false, false, false, false, false, false] 99).length = if (99 : Nat) = 0 then 1 else (8 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_5_0
example : (wordListW (width := 1) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 0).length = if (0 : Nat) = 0 then 1 else (17 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_5_1
example : (wordListW (width := 1) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 1).length = if (1 : Nat) = 0 then 1 else (17 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_5_2
example : (wordListW (width := 1) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 2).length = if (2 : Nat) = 0 then 1 else (17 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_5_7
example : (wordListW (width := 1) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 7).length = if (7 : Nat) = 0 then 1 else (17 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_5_80
example : (wordListW (width := 1) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 80).length = if (80 : Nat) = 0 then 1 else (17 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_5_99
example : (wordListW (width := 1) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 99).length = if (99 : Nat) = 0 then 1 else (17 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_6_0
example : (wordListW (width := 1) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 0).length = if (0 : Nat) = 0 then 1 else (81 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_6_1
example : (wordListW (width := 1) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 1).length = if (1 : Nat) = 0 then 1 else (81 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_6_2
example : (wordListW (width := 1) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 2).length = if (2 : Nat) = 0 then 1 else (81 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_6_7
example : (wordListW (width := 1) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 7).length = if (7 : Nat) = 0 then 1 else (81 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_6_80
example : (wordListW (width := 1) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 80).length = if (80 : Nat) = 0 then 1 else (81 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_1_6_99
example : (wordListW (width := 1) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 99).length = if (99 : Nat) = 0 then 1 else (81 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_0_0
example : (wordListW (width := 2) [] 0).length = if (0 : Nat) = 0 then 1 else (0 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_0_1
example : (wordListW (width := 2) [] 1).length = if (1 : Nat) = 0 then 1 else (0 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_0_2
example : (wordListW (width := 2) [] 2).length = if (2 : Nat) = 0 then 1 else (0 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_0_7
example : (wordListW (width := 2) [] 7).length = if (7 : Nat) = 0 then 1 else (0 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_0_80
example : (wordListW (width := 2) [] 80).length = if (80 : Nat) = 0 then 1 else (0 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_0_99
example : (wordListW (width := 2) [] 99).length = if (99 : Nat) = 0 then 1 else (0 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_1_0
example : (wordListW (width := 2) [true] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_1_1
example : (wordListW (width := 2) [true] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_1_2
example : (wordListW (width := 2) [true] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_1_7
example : (wordListW (width := 2) [true] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_1_80
example : (wordListW (width := 2) [true] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_1_99
example : (wordListW (width := 2) [true] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_2_0
example : (wordListW (width := 2) [false] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_2_1
example : (wordListW (width := 2) [false] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_2_2
example : (wordListW (width := 2) [false] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_2_7
example : (wordListW (width := 2) [false] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_2_80
example : (wordListW (width := 2) [false] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_2_99
example : (wordListW (width := 2) [false] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_3_0
example : (wordListW (width := 2) [true, false, true] 0).length = if (0 : Nat) = 0 then 1 else (3 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_3_1
example : (wordListW (width := 2) [true, false, true] 1).length = if (1 : Nat) = 0 then 1 else (3 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_3_2
example : (wordListW (width := 2) [true, false, true] 2).length = if (2 : Nat) = 0 then 1 else (3 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_3_7
example : (wordListW (width := 2) [true, false, true] 7).length = if (7 : Nat) = 0 then 1 else (3 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_3_80
example : (wordListW (width := 2) [true, false, true] 80).length = if (80 : Nat) = 0 then 1 else (3 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_3_99
example : (wordListW (width := 2) [true, false, true] 99).length = if (99 : Nat) = 0 then 1 else (3 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_4_0
example : (wordListW (width := 2) [false, false, false, false, false, false, false, false] 0).length = if (0 : Nat) = 0 then 1 else (8 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_4_1
example : (wordListW (width := 2) [false, false, false, false, false, false, false, false] 1).length = if (1 : Nat) = 0 then 1 else (8 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_4_2
example : (wordListW (width := 2) [false, false, false, false, false, false, false, false] 2).length = if (2 : Nat) = 0 then 1 else (8 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_4_7
example : (wordListW (width := 2) [false, false, false, false, false, false, false, false] 7).length = if (7 : Nat) = 0 then 1 else (8 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_4_80
example : (wordListW (width := 2) [false, false, false, false, false, false, false, false] 80).length = if (80 : Nat) = 0 then 1 else (8 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_4_99
example : (wordListW (width := 2) [false, false, false, false, false, false, false, false] 99).length = if (99 : Nat) = 0 then 1 else (8 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_5_0
example : (wordListW (width := 2) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 0).length = if (0 : Nat) = 0 then 1 else (17 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_5_1
example : (wordListW (width := 2) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 1).length = if (1 : Nat) = 0 then 1 else (17 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_5_2
example : (wordListW (width := 2) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 2).length = if (2 : Nat) = 0 then 1 else (17 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_5_7
example : (wordListW (width := 2) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 7).length = if (7 : Nat) = 0 then 1 else (17 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_5_80
example : (wordListW (width := 2) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 80).length = if (80 : Nat) = 0 then 1 else (17 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_5_99
example : (wordListW (width := 2) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 99).length = if (99 : Nat) = 0 then 1 else (17 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_6_0
example : (wordListW (width := 2) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 0).length = if (0 : Nat) = 0 then 1 else (81 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_6_1
example : (wordListW (width := 2) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 1).length = if (1 : Nat) = 0 then 1 else (81 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_6_2
example : (wordListW (width := 2) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 2).length = if (2 : Nat) = 0 then 1 else (81 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_6_7
example : (wordListW (width := 2) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 7).length = if (7 : Nat) = 0 then 1 else (81 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_6_80
example : (wordListW (width := 2) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 80).length = if (80 : Nat) = 0 then 1 else (81 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_2_6_99
example : (wordListW (width := 2) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 99).length = if (99 : Nat) = 0 then 1 else (81 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_0_0
example : (wordListW (width := 8) [] 0).length = if (0 : Nat) = 0 then 1 else (0 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_0_1
example : (wordListW (width := 8) [] 1).length = if (1 : Nat) = 0 then 1 else (0 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_0_2
example : (wordListW (width := 8) [] 2).length = if (2 : Nat) = 0 then 1 else (0 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_0_7
example : (wordListW (width := 8) [] 7).length = if (7 : Nat) = 0 then 1 else (0 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_0_80
example : (wordListW (width := 8) [] 80).length = if (80 : Nat) = 0 then 1 else (0 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_0_99
example : (wordListW (width := 8) [] 99).length = if (99 : Nat) = 0 then 1 else (0 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_1_0
example : (wordListW (width := 8) [true] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_1_1
example : (wordListW (width := 8) [true] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_1_2
example : (wordListW (width := 8) [true] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_1_7
example : (wordListW (width := 8) [true] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_1_80
example : (wordListW (width := 8) [true] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_1_99
example : (wordListW (width := 8) [true] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_2_0
example : (wordListW (width := 8) [false] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_2_1
example : (wordListW (width := 8) [false] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_2_2
example : (wordListW (width := 8) [false] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_2_7
example : (wordListW (width := 8) [false] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_2_80
example : (wordListW (width := 8) [false] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_2_99
example : (wordListW (width := 8) [false] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_3_0
example : (wordListW (width := 8) [true, false, true] 0).length = if (0 : Nat) = 0 then 1 else (3 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_3_1
example : (wordListW (width := 8) [true, false, true] 1).length = if (1 : Nat) = 0 then 1 else (3 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_3_2
example : (wordListW (width := 8) [true, false, true] 2).length = if (2 : Nat) = 0 then 1 else (3 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_3_7
example : (wordListW (width := 8) [true, false, true] 7).length = if (7 : Nat) = 0 then 1 else (3 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_3_80
example : (wordListW (width := 8) [true, false, true] 80).length = if (80 : Nat) = 0 then 1 else (3 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_3_99
example : (wordListW (width := 8) [true, false, true] 99).length = if (99 : Nat) = 0 then 1 else (3 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_4_0
example : (wordListW (width := 8) [false, false, false, false, false, false, false, false] 0).length = if (0 : Nat) = 0 then 1 else (8 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_4_1
example : (wordListW (width := 8) [false, false, false, false, false, false, false, false] 1).length = if (1 : Nat) = 0 then 1 else (8 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_4_2
example : (wordListW (width := 8) [false, false, false, false, false, false, false, false] 2).length = if (2 : Nat) = 0 then 1 else (8 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_4_7
example : (wordListW (width := 8) [false, false, false, false, false, false, false, false] 7).length = if (7 : Nat) = 0 then 1 else (8 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_4_80
example : (wordListW (width := 8) [false, false, false, false, false, false, false, false] 80).length = if (80 : Nat) = 0 then 1 else (8 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_4_99
example : (wordListW (width := 8) [false, false, false, false, false, false, false, false] 99).length = if (99 : Nat) = 0 then 1 else (8 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_5_0
example : (wordListW (width := 8) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 0).length = if (0 : Nat) = 0 then 1 else (17 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_5_1
example : (wordListW (width := 8) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 1).length = if (1 : Nat) = 0 then 1 else (17 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_5_2
example : (wordListW (width := 8) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 2).length = if (2 : Nat) = 0 then 1 else (17 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_5_7
example : (wordListW (width := 8) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 7).length = if (7 : Nat) = 0 then 1 else (17 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_5_80
example : (wordListW (width := 8) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 80).length = if (80 : Nat) = 0 then 1 else (17 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_5_99
example : (wordListW (width := 8) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 99).length = if (99 : Nat) = 0 then 1 else (17 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_6_0
example : (wordListW (width := 8) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 0).length = if (0 : Nat) = 0 then 1 else (81 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_6_1
example : (wordListW (width := 8) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 1).length = if (1 : Nat) = 0 then 1 else (81 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_6_2
example : (wordListW (width := 8) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 2).length = if (2 : Nat) = 0 then 1 else (81 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_6_7
example : (wordListW (width := 8) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 7).length = if (7 : Nat) = 0 then 1 else (81 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_6_80
example : (wordListW (width := 8) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 80).length = if (80 : Nat) = 0 then 1 else (81 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_8_6_99
example : (wordListW (width := 8) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 99).length = if (99 : Nat) = 0 then 1 else (81 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_0_0
example : (wordListW (width := 64) [] 0).length = if (0 : Nat) = 0 then 1 else (0 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_0_1
example : (wordListW (width := 64) [] 1).length = if (1 : Nat) = 0 then 1 else (0 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_0_2
example : (wordListW (width := 64) [] 2).length = if (2 : Nat) = 0 then 1 else (0 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_0_7
example : (wordListW (width := 64) [] 7).length = if (7 : Nat) = 0 then 1 else (0 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_0_80
example : (wordListW (width := 64) [] 80).length = if (80 : Nat) = 0 then 1 else (0 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_0_99
example : (wordListW (width := 64) [] 99).length = if (99 : Nat) = 0 then 1 else (0 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_1_0
example : (wordListW (width := 64) [true] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_1_1
example : (wordListW (width := 64) [true] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_1_2
example : (wordListW (width := 64) [true] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_1_7
example : (wordListW (width := 64) [true] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_1_80
example : (wordListW (width := 64) [true] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_1_99
example : (wordListW (width := 64) [true] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_2_0
example : (wordListW (width := 64) [false] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_2_1
example : (wordListW (width := 64) [false] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_2_2
example : (wordListW (width := 64) [false] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_2_7
example : (wordListW (width := 64) [false] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_2_80
example : (wordListW (width := 64) [false] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_2_99
example : (wordListW (width := 64) [false] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_3_0
example : (wordListW (width := 64) [true, false, true] 0).length = if (0 : Nat) = 0 then 1 else (3 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_3_1
example : (wordListW (width := 64) [true, false, true] 1).length = if (1 : Nat) = 0 then 1 else (3 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_3_2
example : (wordListW (width := 64) [true, false, true] 2).length = if (2 : Nat) = 0 then 1 else (3 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_3_7
example : (wordListW (width := 64) [true, false, true] 7).length = if (7 : Nat) = 0 then 1 else (3 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_3_80
example : (wordListW (width := 64) [true, false, true] 80).length = if (80 : Nat) = 0 then 1 else (3 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_3_99
example : (wordListW (width := 64) [true, false, true] 99).length = if (99 : Nat) = 0 then 1 else (3 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_4_0
example : (wordListW (width := 64) [false, false, false, false, false, false, false, false] 0).length = if (0 : Nat) = 0 then 1 else (8 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_4_1
example : (wordListW (width := 64) [false, false, false, false, false, false, false, false] 1).length = if (1 : Nat) = 0 then 1 else (8 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_4_2
example : (wordListW (width := 64) [false, false, false, false, false, false, false, false] 2).length = if (2 : Nat) = 0 then 1 else (8 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_4_7
example : (wordListW (width := 64) [false, false, false, false, false, false, false, false] 7).length = if (7 : Nat) = 0 then 1 else (8 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_4_80
example : (wordListW (width := 64) [false, false, false, false, false, false, false, false] 80).length = if (80 : Nat) = 0 then 1 else (8 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_4_99
example : (wordListW (width := 64) [false, false, false, false, false, false, false, false] 99).length = if (99 : Nat) = 0 then 1 else (8 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_5_0
example : (wordListW (width := 64) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 0).length = if (0 : Nat) = 0 then 1 else (17 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_5_1
example : (wordListW (width := 64) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 1).length = if (1 : Nat) = 0 then 1 else (17 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_5_2
example : (wordListW (width := 64) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 2).length = if (2 : Nat) = 0 then 1 else (17 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_5_7
example : (wordListW (width := 64) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 7).length = if (7 : Nat) = 0 then 1 else (17 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_5_80
example : (wordListW (width := 64) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 80).length = if (80 : Nat) = 0 then 1 else (17 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_5_99
example : (wordListW (width := 64) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 99).length = if (99 : Nat) = 0 then 1 else (17 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_6_0
example : (wordListW (width := 64) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 0).length = if (0 : Nat) = 0 then 1 else (81 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_6_1
example : (wordListW (width := 64) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 1).length = if (1 : Nat) = 0 then 1 else (81 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_6_2
example : (wordListW (width := 64) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 2).length = if (2 : Nat) = 0 then 1 else (81 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_6_7
example : (wordListW (width := 64) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 7).length = if (7 : Nat) = 0 then 1 else (81 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_6_80
example : (wordListW (width := 64) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 80).length = if (80 : Nat) = 0 then 1 else (81 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_64_6_99
example : (wordListW (width := 64) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 99).length = if (99 : Nat) = 0 then 1 else (81 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_0_0
example : (wordListW (width := 80) [] 0).length = if (0 : Nat) = 0 then 1 else (0 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_0_1
example : (wordListW (width := 80) [] 1).length = if (1 : Nat) = 0 then 1 else (0 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_0_2
example : (wordListW (width := 80) [] 2).length = if (2 : Nat) = 0 then 1 else (0 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_0_7
example : (wordListW (width := 80) [] 7).length = if (7 : Nat) = 0 then 1 else (0 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_0_80
example : (wordListW (width := 80) [] 80).length = if (80 : Nat) = 0 then 1 else (0 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_0_99
example : (wordListW (width := 80) [] 99).length = if (99 : Nat) = 0 then 1 else (0 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_1_0
example : (wordListW (width := 80) [true] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_1_1
example : (wordListW (width := 80) [true] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_1_2
example : (wordListW (width := 80) [true] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_1_7
example : (wordListW (width := 80) [true] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_1_80
example : (wordListW (width := 80) [true] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_1_99
example : (wordListW (width := 80) [true] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_2_0
example : (wordListW (width := 80) [false] 0).length = if (0 : Nat) = 0 then 1 else (1 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_2_1
example : (wordListW (width := 80) [false] 1).length = if (1 : Nat) = 0 then 1 else (1 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_2_2
example : (wordListW (width := 80) [false] 2).length = if (2 : Nat) = 0 then 1 else (1 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_2_7
example : (wordListW (width := 80) [false] 7).length = if (7 : Nat) = 0 then 1 else (1 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_2_80
example : (wordListW (width := 80) [false] 80).length = if (80 : Nat) = 0 then 1 else (1 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_2_99
example : (wordListW (width := 80) [false] 99).length = if (99 : Nat) = 0 then 1 else (1 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_3_0
example : (wordListW (width := 80) [true, false, true] 0).length = if (0 : Nat) = 0 then 1 else (3 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_3_1
example : (wordListW (width := 80) [true, false, true] 1).length = if (1 : Nat) = 0 then 1 else (3 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_3_2
example : (wordListW (width := 80) [true, false, true] 2).length = if (2 : Nat) = 0 then 1 else (3 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_3_7
example : (wordListW (width := 80) [true, false, true] 7).length = if (7 : Nat) = 0 then 1 else (3 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_3_80
example : (wordListW (width := 80) [true, false, true] 80).length = if (80 : Nat) = 0 then 1 else (3 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_3_99
example : (wordListW (width := 80) [true, false, true] 99).length = if (99 : Nat) = 0 then 1 else (3 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_4_0
example : (wordListW (width := 80) [false, false, false, false, false, false, false, false] 0).length = if (0 : Nat) = 0 then 1 else (8 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_4_1
example : (wordListW (width := 80) [false, false, false, false, false, false, false, false] 1).length = if (1 : Nat) = 0 then 1 else (8 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_4_2
example : (wordListW (width := 80) [false, false, false, false, false, false, false, false] 2).length = if (2 : Nat) = 0 then 1 else (8 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_4_7
example : (wordListW (width := 80) [false, false, false, false, false, false, false, false] 7).length = if (7 : Nat) = 0 then 1 else (8 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_4_80
example : (wordListW (width := 80) [false, false, false, false, false, false, false, false] 80).length = if (80 : Nat) = 0 then 1 else (8 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_4_99
example : (wordListW (width := 80) [false, false, false, false, false, false, false, false] 99).length = if (99 : Nat) = 0 then 1 else (8 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_5_0
example : (wordListW (width := 80) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 0).length = if (0 : Nat) = 0 then 1 else (17 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_5_1
example : (wordListW (width := 80) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 1).length = if (1 : Nat) = 0 then 1 else (17 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_5_2
example : (wordListW (width := 80) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 2).length = if (2 : Nat) = 0 then 1 else (17 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_5_7
example : (wordListW (width := 80) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 7).length = if (7 : Nat) = 0 then 1 else (17 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_5_80
example : (wordListW (width := 80) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 80).length = if (80 : Nat) = 0 then 1 else (17 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_5_99
example : (wordListW (width := 80) [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true] 99).length = if (99 : Nat) = 0 then 1 else (17 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_6_0
example : (wordListW (width := 80) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 0).length = if (0 : Nat) = 0 then 1 else (81 - 1) / 0 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_6_1
example : (wordListW (width := 80) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 1).length = if (1 : Nat) = 0 then 1 else (81 - 1) / 1 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_6_2
example : (wordListW (width := 80) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 2).length = if (2 : Nat) = 0 then 1 else (81 - 1) / 2 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_6_7
example : (wordListW (width := 80) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 7).length = if (7 : Nat) = 0 then 1 else (81 - 1) / 7 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_6_80
example : (wordListW (width := 80) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 80).length = if (80 : Nat) = 0 then 1 else (81 - 1) / 80 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_length_80_6_99
example : (wordListW (width := 80) [true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false, true, false, false] 99).length = if (99 : Nat) = 0 then 1 else (81 - 1) / 99 + 1 := by simp +decide [wordListW, bitsToWordW] <;> decide +kernel

-- wl_div_0_0
example : 0 < (0 : Nat) → (0 : Nat) / 0 + 1 = (0 + 0) / 0 := by decide

-- wl_div_0_1
example : 0 < (1 : Nat) → (0 : Nat) / 1 + 1 = (0 + 1) / 1 := by decide

-- wl_div_0_2
example : 0 < (2 : Nat) → (0 : Nat) / 2 + 1 = (0 + 2) / 2 := by decide

-- wl_div_0_7
example : 0 < (7 : Nat) → (0 : Nat) / 7 + 1 = (0 + 7) / 7 := by decide

-- wl_div_0_80
example : 0 < (80 : Nat) → (0 : Nat) / 80 + 1 = (0 + 80) / 80 := by decide

-- wl_div_0_99
example : 0 < (99 : Nat) → (0 : Nat) / 99 + 1 = (0 + 99) / 99 := by decide

-- wl_div_1_0
example : 0 < (0 : Nat) → (1 : Nat) / 0 + 1 = (1 + 0) / 0 := by decide

-- wl_div_1_1
example : 0 < (1 : Nat) → (1 : Nat) / 1 + 1 = (1 + 1) / 1 := by decide

-- wl_div_1_2
example : 0 < (2 : Nat) → (1 : Nat) / 2 + 1 = (1 + 2) / 2 := by decide

-- wl_div_1_7
example : 0 < (7 : Nat) → (1 : Nat) / 7 + 1 = (1 + 7) / 7 := by decide

-- wl_div_1_80
example : 0 < (80 : Nat) → (1 : Nat) / 80 + 1 = (1 + 80) / 80 := by decide

-- wl_div_1_99
example : 0 < (99 : Nat) → (1 : Nat) / 99 + 1 = (1 + 99) / 99 := by decide

-- wl_div_2_0
example : 0 < (0 : Nat) → (2 : Nat) / 0 + 1 = (2 + 0) / 0 := by decide

-- wl_div_2_1
example : 0 < (1 : Nat) → (2 : Nat) / 1 + 1 = (2 + 1) / 1 := by decide

-- wl_div_2_2
example : 0 < (2 : Nat) → (2 : Nat) / 2 + 1 = (2 + 2) / 2 := by decide

-- wl_div_2_7
example : 0 < (7 : Nat) → (2 : Nat) / 7 + 1 = (2 + 7) / 7 := by decide

-- wl_div_2_80
example : 0 < (80 : Nat) → (2 : Nat) / 80 + 1 = (2 + 80) / 80 := by decide

-- wl_div_2_99
example : 0 < (99 : Nat) → (2 : Nat) / 99 + 1 = (2 + 99) / 99 := by decide

-- wl_div_3_0
example : 0 < (0 : Nat) → (7 : Nat) / 0 + 1 = (7 + 0) / 0 := by decide

-- wl_div_3_1
example : 0 < (1 : Nat) → (7 : Nat) / 1 + 1 = (7 + 1) / 1 := by decide

-- wl_div_3_2
example : 0 < (2 : Nat) → (7 : Nat) / 2 + 1 = (7 + 2) / 2 := by decide

-- wl_div_3_7
example : 0 < (7 : Nat) → (7 : Nat) / 7 + 1 = (7 + 7) / 7 := by decide

-- wl_div_3_80
example : 0 < (80 : Nat) → (7 : Nat) / 80 + 1 = (7 + 80) / 80 := by decide

-- wl_div_3_99
example : 0 < (99 : Nat) → (7 : Nat) / 99 + 1 = (7 + 99) / 99 := by decide

-- wl_div_4_0
example : 0 < (0 : Nat) → (1208925819614629174706176 : Nat) / 0 + 1 = (1208925819614629174706176 + 0) / 0 := by decide

-- wl_div_4_1
example : 0 < (1 : Nat) → (1208925819614629174706176 : Nat) / 1 + 1 = (1208925819614629174706176 + 1) / 1 := by decide

-- wl_div_4_2
example : 0 < (2 : Nat) → (1208925819614629174706176 : Nat) / 2 + 1 = (1208925819614629174706176 + 2) / 2 := by decide

-- wl_div_4_7
example : 0 < (7 : Nat) → (1208925819614629174706176 : Nat) / 7 + 1 = (1208925819614629174706176 + 7) / 7 := by decide

-- wl_div_4_80
example : 0 < (80 : Nat) → (1208925819614629174706176 : Nat) / 80 + 1 = (1208925819614629174706176 + 80) / 80 := by decide

-- wl_div_4_99
example : 0 < (99 : Nat) → (1208925819614629174706176 : Nat) / 99 + 1 = (1208925819614629174706176 + 99) / 99 := by decide

-- wl_div_5_0
example : 0 < (0 : Nat) → (1208925819614629174706177 : Nat) / 0 + 1 = (1208925819614629174706177 + 0) / 0 := by decide

-- wl_div_5_1
example : 0 < (1 : Nat) → (1208925819614629174706177 : Nat) / 1 + 1 = (1208925819614629174706177 + 1) / 1 := by decide

-- wl_div_5_2
example : 0 < (2 : Nat) → (1208925819614629174706177 : Nat) / 2 + 1 = (1208925819614629174706177 + 2) / 2 := by decide

-- wl_div_5_7
example : 0 < (7 : Nat) → (1208925819614629174706177 : Nat) / 7 + 1 = (1208925819614629174706177 + 7) / 7 := by decide

-- wl_div_5_80
example : 0 < (80 : Nat) → (1208925819614629174706177 : Nat) / 80 + 1 = (1208925819614629174706177 + 80) / 80 := by decide

-- wl_div_5_99
example : 0 < (99 : Nat) → (1208925819614629174706177 : Nat) / 99 + 1 = (1208925819614629174706177 + 99) / 99 := by decide

example {width : Nat} [NeZero width] (xs : List Bool) (d : Nat) :
    (wordListW xs d : List (BitVec width)).length = if d = 0 then 1 else (xs.length - 1) / d + 1 :=
  lengthWordList xs d


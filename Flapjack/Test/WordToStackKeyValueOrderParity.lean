import Flapjack.Compiler.Backend.WordToStack.Proofs.KeyValueOrder
open Flapjack Flapjack.Compiler.Backend.WordToStack

-- kv_value_0_0_1
example : wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (0, .word (0 : BitVec 1)) = true := by decide

-- kv_value_0_1_1
example : wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (0, .word (1 : BitVec 1)) = false := by decide

-- kv_value_0_2_1
example : wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (0, .word (1 : BitVec 1)) = false := by decide

-- kv_value_0_3_1
example : wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (0, .loc 0 0) = true := by decide

-- kv_value_0_4_1
example : wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (0, .loc 0 1) = true := by decide

-- kv_value_0_5_1
example : wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (0, .loc 1 0) = true := by decide

-- kv_value_0_6_1
example : wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (1, .word (0 : BitVec 1)) = false := by decide

-- kv_value_0_7_1
example : wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (2, .loc 0 0) = false := by decide

-- kv_value_1_0_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (0 : BitVec 1)) = true := by decide

-- kv_value_1_1_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (1 : BitVec 1)) = true := by decide

-- kv_value_1_2_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (1 : BitVec 1)) = true := by decide

-- kv_value_1_3_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 0 0) = true := by decide

-- kv_value_1_4_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 0 1) = true := by decide

-- kv_value_1_5_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 1 0) = true := by decide

-- kv_value_1_6_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (1, .word (0 : BitVec 1)) = false := by decide

-- kv_value_1_7_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (2, .loc 0 0) = false := by decide

-- kv_value_2_0_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (0 : BitVec 1)) = true := by decide

-- kv_value_2_1_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (1 : BitVec 1)) = true := by decide

-- kv_value_2_2_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (1 : BitVec 1)) = true := by decide

-- kv_value_2_3_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 0 0) = true := by decide

-- kv_value_2_4_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 0 1) = true := by decide

-- kv_value_2_5_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 1 0) = true := by decide

-- kv_value_2_6_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (1, .word (0 : BitVec 1)) = false := by decide

-- kv_value_2_7_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (2, .loc 0 0) = false := by decide

-- kv_value_3_0_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .word (0 : BitVec 1)) = false := by decide

-- kv_value_3_1_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .word (1 : BitVec 1)) = false := by decide

-- kv_value_3_2_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .word (1 : BitVec 1)) = false := by decide

-- kv_value_3_3_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_3_4_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .loc 0 1) = false := by decide

-- kv_value_3_5_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .loc 1 0) = false := by decide

-- kv_value_3_6_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (1, .word (0 : BitVec 1)) = false := by decide

-- kv_value_3_7_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (2, .loc 0 0) = false := by decide

-- kv_value_4_0_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 1) (0, .word (0 : BitVec 1)) = false := by decide

-- kv_value_4_1_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 1) (0, .word (1 : BitVec 1)) = false := by decide

-- kv_value_4_2_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 1) (0, .word (1 : BitVec 1)) = false := by decide

-- kv_value_4_3_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 1) (0, .loc 0 0) = true := by decide

-- kv_value_4_4_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 1) (0, .loc 0 1) = true := by decide

-- kv_value_4_5_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 1) (0, .loc 1 0) = false := by decide

-- kv_value_4_6_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 1) (1, .word (0 : BitVec 1)) = false := by decide

-- kv_value_4_7_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 1) (2, .loc 0 0) = false := by decide

-- kv_value_5_0_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .word (0 : BitVec 1)) = false := by decide

-- kv_value_5_1_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .word (1 : BitVec 1)) = false := by decide

-- kv_value_5_2_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .word (1 : BitVec 1)) = false := by decide

-- kv_value_5_3_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .loc 0 0) = true := by decide

-- kv_value_5_4_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .loc 0 1) = true := by decide

-- kv_value_5_5_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .loc 1 0) = true := by decide

-- kv_value_5_6_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (1, .word (0 : BitVec 1)) = false := by decide

-- kv_value_5_7_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (2, .loc 0 0) = false := by decide

-- kv_value_6_0_1
example : wordSemKeyValCompare (width := 1) (1, .word (0 : BitVec 1)) (0, .word (0 : BitVec 1)) = true := by decide

-- kv_value_6_1_1
example : wordSemKeyValCompare (width := 1) (1, .word (0 : BitVec 1)) (0, .word (1 : BitVec 1)) = true := by decide

-- kv_value_6_2_1
example : wordSemKeyValCompare (width := 1) (1, .word (0 : BitVec 1)) (0, .word (1 : BitVec 1)) = true := by decide

-- kv_value_6_3_1
example : wordSemKeyValCompare (width := 1) (1, .word (0 : BitVec 1)) (0, .loc 0 0) = true := by decide

-- kv_value_6_4_1
example : wordSemKeyValCompare (width := 1) (1, .word (0 : BitVec 1)) (0, .loc 0 1) = true := by decide

-- kv_value_6_5_1
example : wordSemKeyValCompare (width := 1) (1, .word (0 : BitVec 1)) (0, .loc 1 0) = true := by decide

-- kv_value_6_6_1
example : wordSemKeyValCompare (width := 1) (1, .word (0 : BitVec 1)) (1, .word (0 : BitVec 1)) = true := by decide

-- kv_value_6_7_1
example : wordSemKeyValCompare (width := 1) (1, .word (0 : BitVec 1)) (2, .loc 0 0) = false := by decide

-- kv_value_7_0_1
example : wordSemKeyValCompare (width := 1) (2, .loc 0 0) (0, .word (0 : BitVec 1)) = true := by decide

-- kv_value_7_1_1
example : wordSemKeyValCompare (width := 1) (2, .loc 0 0) (0, .word (1 : BitVec 1)) = true := by decide

-- kv_value_7_2_1
example : wordSemKeyValCompare (width := 1) (2, .loc 0 0) (0, .word (1 : BitVec 1)) = true := by decide

-- kv_value_7_3_1
example : wordSemKeyValCompare (width := 1) (2, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_7_4_1
example : wordSemKeyValCompare (width := 1) (2, .loc 0 0) (0, .loc 0 1) = true := by decide

-- kv_value_7_5_1
example : wordSemKeyValCompare (width := 1) (2, .loc 0 0) (0, .loc 1 0) = true := by decide

-- kv_value_7_6_1
example : wordSemKeyValCompare (width := 1) (2, .loc 0 0) (1, .word (0 : BitVec 1)) = true := by decide

-- kv_value_7_7_1
example : wordSemKeyValCompare (width := 1) (2, .loc 0 0) (2, .loc 0 0) = true := by decide

-- kv_transit_0_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (0 : BitVec 1)) = true → wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (0, .word (1 : BitVec 1)) = true → wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (1 : BitVec 1)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_1_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (0 : BitVec 1)) = true → wordSemKeyValCompare (width := 1) (0, .word (0 : BitVec 1)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

-- kv_transit_2_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .word (0 : BitVec 1)) = true → wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (0 : BitVec 1)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_3_1
example : wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_4_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .word (1 : BitVec 1)) = true → wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .word (0 : BitVec 1)) = true → wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .word (0 : BitVec 1)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_5_1
example : wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .word (1 : BitVec 1)) = true → wordSemKeyValCompare (width := 1) (0, .word (1 : BitVec 1)) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 1) (0, .loc 0 0) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_6_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 1) (0, .loc 0 1) (0, .word (0 : BitVec 1)) = true → wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .word (0 : BitVec 1)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_7_1
example : wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 1) (0, .loc 0 1) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 1) (0, .loc 1 0) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

-- kv_value_0_0_2
example : wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (0, .word (0 : BitVec 2)) = true := by decide

-- kv_value_0_1_2
example : wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (0, .word (3 : BitVec 2)) = false := by decide

-- kv_value_0_2_2
example : wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (0, .word (2 : BitVec 2)) = false := by decide

-- kv_value_0_3_2
example : wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (0, .loc 0 0) = true := by decide

-- kv_value_0_4_2
example : wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (0, .loc 0 1) = true := by decide

-- kv_value_0_5_2
example : wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (0, .loc 1 0) = true := by decide

-- kv_value_0_6_2
example : wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (1, .word (0 : BitVec 2)) = false := by decide

-- kv_value_0_7_2
example : wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (2, .loc 0 0) = false := by decide

-- kv_value_1_0_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .word (0 : BitVec 2)) = true := by decide

-- kv_value_1_1_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .word (3 : BitVec 2)) = true := by decide

-- kv_value_1_2_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .word (2 : BitVec 2)) = false := by decide

-- kv_value_1_3_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .loc 0 0) = true := by decide

-- kv_value_1_4_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .loc 0 1) = true := by decide

-- kv_value_1_5_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .loc 1 0) = true := by decide

-- kv_value_1_6_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (1, .word (0 : BitVec 2)) = false := by decide

-- kv_value_1_7_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (2, .loc 0 0) = false := by decide

-- kv_value_2_0_2
example : wordSemKeyValCompare (width := 2) (0, .word (2 : BitVec 2)) (0, .word (0 : BitVec 2)) = true := by decide

-- kv_value_2_1_2
example : wordSemKeyValCompare (width := 2) (0, .word (2 : BitVec 2)) (0, .word (3 : BitVec 2)) = true := by decide

-- kv_value_2_2_2
example : wordSemKeyValCompare (width := 2) (0, .word (2 : BitVec 2)) (0, .word (2 : BitVec 2)) = true := by decide

-- kv_value_2_3_2
example : wordSemKeyValCompare (width := 2) (0, .word (2 : BitVec 2)) (0, .loc 0 0) = true := by decide

-- kv_value_2_4_2
example : wordSemKeyValCompare (width := 2) (0, .word (2 : BitVec 2)) (0, .loc 0 1) = true := by decide

-- kv_value_2_5_2
example : wordSemKeyValCompare (width := 2) (0, .word (2 : BitVec 2)) (0, .loc 1 0) = true := by decide

-- kv_value_2_6_2
example : wordSemKeyValCompare (width := 2) (0, .word (2 : BitVec 2)) (1, .word (0 : BitVec 2)) = false := by decide

-- kv_value_2_7_2
example : wordSemKeyValCompare (width := 2) (0, .word (2 : BitVec 2)) (2, .loc 0 0) = false := by decide

-- kv_value_3_0_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .word (0 : BitVec 2)) = false := by decide

-- kv_value_3_1_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .word (3 : BitVec 2)) = false := by decide

-- kv_value_3_2_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .word (2 : BitVec 2)) = false := by decide

-- kv_value_3_3_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_3_4_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .loc 0 1) = false := by decide

-- kv_value_3_5_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .loc 1 0) = false := by decide

-- kv_value_3_6_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (1, .word (0 : BitVec 2)) = false := by decide

-- kv_value_3_7_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (2, .loc 0 0) = false := by decide

-- kv_value_4_0_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 1) (0, .word (0 : BitVec 2)) = false := by decide

-- kv_value_4_1_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 1) (0, .word (3 : BitVec 2)) = false := by decide

-- kv_value_4_2_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 1) (0, .word (2 : BitVec 2)) = false := by decide

-- kv_value_4_3_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 1) (0, .loc 0 0) = true := by decide

-- kv_value_4_4_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 1) (0, .loc 0 1) = true := by decide

-- kv_value_4_5_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 1) (0, .loc 1 0) = false := by decide

-- kv_value_4_6_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 1) (1, .word (0 : BitVec 2)) = false := by decide

-- kv_value_4_7_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 1) (2, .loc 0 0) = false := by decide

-- kv_value_5_0_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .word (0 : BitVec 2)) = false := by decide

-- kv_value_5_1_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .word (3 : BitVec 2)) = false := by decide

-- kv_value_5_2_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .word (2 : BitVec 2)) = false := by decide

-- kv_value_5_3_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .loc 0 0) = true := by decide

-- kv_value_5_4_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .loc 0 1) = true := by decide

-- kv_value_5_5_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .loc 1 0) = true := by decide

-- kv_value_5_6_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (1, .word (0 : BitVec 2)) = false := by decide

-- kv_value_5_7_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (2, .loc 0 0) = false := by decide

-- kv_value_6_0_2
example : wordSemKeyValCompare (width := 2) (1, .word (0 : BitVec 2)) (0, .word (0 : BitVec 2)) = true := by decide

-- kv_value_6_1_2
example : wordSemKeyValCompare (width := 2) (1, .word (0 : BitVec 2)) (0, .word (3 : BitVec 2)) = true := by decide

-- kv_value_6_2_2
example : wordSemKeyValCompare (width := 2) (1, .word (0 : BitVec 2)) (0, .word (2 : BitVec 2)) = true := by decide

-- kv_value_6_3_2
example : wordSemKeyValCompare (width := 2) (1, .word (0 : BitVec 2)) (0, .loc 0 0) = true := by decide

-- kv_value_6_4_2
example : wordSemKeyValCompare (width := 2) (1, .word (0 : BitVec 2)) (0, .loc 0 1) = true := by decide

-- kv_value_6_5_2
example : wordSemKeyValCompare (width := 2) (1, .word (0 : BitVec 2)) (0, .loc 1 0) = true := by decide

-- kv_value_6_6_2
example : wordSemKeyValCompare (width := 2) (1, .word (0 : BitVec 2)) (1, .word (0 : BitVec 2)) = true := by decide

-- kv_value_6_7_2
example : wordSemKeyValCompare (width := 2) (1, .word (0 : BitVec 2)) (2, .loc 0 0) = false := by decide

-- kv_value_7_0_2
example : wordSemKeyValCompare (width := 2) (2, .loc 0 0) (0, .word (0 : BitVec 2)) = true := by decide

-- kv_value_7_1_2
example : wordSemKeyValCompare (width := 2) (2, .loc 0 0) (0, .word (3 : BitVec 2)) = true := by decide

-- kv_value_7_2_2
example : wordSemKeyValCompare (width := 2) (2, .loc 0 0) (0, .word (2 : BitVec 2)) = true := by decide

-- kv_value_7_3_2
example : wordSemKeyValCompare (width := 2) (2, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_7_4_2
example : wordSemKeyValCompare (width := 2) (2, .loc 0 0) (0, .loc 0 1) = true := by decide

-- kv_value_7_5_2
example : wordSemKeyValCompare (width := 2) (2, .loc 0 0) (0, .loc 1 0) = true := by decide

-- kv_value_7_6_2
example : wordSemKeyValCompare (width := 2) (2, .loc 0 0) (1, .word (0 : BitVec 2)) = true := by decide

-- kv_value_7_7_2
example : wordSemKeyValCompare (width := 2) (2, .loc 0 0) (2, .loc 0 0) = true := by decide

-- kv_transit_0_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .word (0 : BitVec 2)) = true → wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (0, .word (2 : BitVec 2)) = true → wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .word (2 : BitVec 2)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_1_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .word (0 : BitVec 2)) = true → wordSemKeyValCompare (width := 2) (0, .word (0 : BitVec 2)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

-- kv_transit_2_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .word (0 : BitVec 2)) = true → wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .word (0 : BitVec 2)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_3_2
example : wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_4_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .word (3 : BitVec 2)) = true → wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .word (0 : BitVec 2)) = true → wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .word (0 : BitVec 2)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_5_2
example : wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .word (3 : BitVec 2)) = true → wordSemKeyValCompare (width := 2) (0, .word (3 : BitVec 2)) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 2) (0, .loc 0 0) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_6_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 2) (0, .loc 0 1) (0, .word (0 : BitVec 2)) = true → wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .word (0 : BitVec 2)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_7_2
example : wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 2) (0, .loc 0 1) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 2) (0, .loc 1 0) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

-- kv_value_0_0_8
example : wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (0, .word (0 : BitVec 8)) = true := by decide

-- kv_value_0_1_8
example : wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (0, .word (255 : BitVec 8)) = false := by decide

-- kv_value_0_2_8
example : wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (0, .word (128 : BitVec 8)) = false := by decide

-- kv_value_0_3_8
example : wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (0, .loc 0 0) = true := by decide

-- kv_value_0_4_8
example : wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (0, .loc 0 1) = true := by decide

-- kv_value_0_5_8
example : wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (0, .loc 1 0) = true := by decide

-- kv_value_0_6_8
example : wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (1, .word (0 : BitVec 8)) = false := by decide

-- kv_value_0_7_8
example : wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (2, .loc 0 0) = false := by decide

-- kv_value_1_0_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .word (0 : BitVec 8)) = true := by decide

-- kv_value_1_1_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .word (255 : BitVec 8)) = true := by decide

-- kv_value_1_2_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .word (128 : BitVec 8)) = false := by decide

-- kv_value_1_3_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .loc 0 0) = true := by decide

-- kv_value_1_4_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .loc 0 1) = true := by decide

-- kv_value_1_5_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .loc 1 0) = true := by decide

-- kv_value_1_6_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (1, .word (0 : BitVec 8)) = false := by decide

-- kv_value_1_7_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (2, .loc 0 0) = false := by decide

-- kv_value_2_0_8
example : wordSemKeyValCompare (width := 8) (0, .word (128 : BitVec 8)) (0, .word (0 : BitVec 8)) = true := by decide

-- kv_value_2_1_8
example : wordSemKeyValCompare (width := 8) (0, .word (128 : BitVec 8)) (0, .word (255 : BitVec 8)) = true := by decide

-- kv_value_2_2_8
example : wordSemKeyValCompare (width := 8) (0, .word (128 : BitVec 8)) (0, .word (128 : BitVec 8)) = true := by decide

-- kv_value_2_3_8
example : wordSemKeyValCompare (width := 8) (0, .word (128 : BitVec 8)) (0, .loc 0 0) = true := by decide

-- kv_value_2_4_8
example : wordSemKeyValCompare (width := 8) (0, .word (128 : BitVec 8)) (0, .loc 0 1) = true := by decide

-- kv_value_2_5_8
example : wordSemKeyValCompare (width := 8) (0, .word (128 : BitVec 8)) (0, .loc 1 0) = true := by decide

-- kv_value_2_6_8
example : wordSemKeyValCompare (width := 8) (0, .word (128 : BitVec 8)) (1, .word (0 : BitVec 8)) = false := by decide

-- kv_value_2_7_8
example : wordSemKeyValCompare (width := 8) (0, .word (128 : BitVec 8)) (2, .loc 0 0) = false := by decide

-- kv_value_3_0_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .word (0 : BitVec 8)) = false := by decide

-- kv_value_3_1_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .word (255 : BitVec 8)) = false := by decide

-- kv_value_3_2_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .word (128 : BitVec 8)) = false := by decide

-- kv_value_3_3_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_3_4_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .loc 0 1) = false := by decide

-- kv_value_3_5_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .loc 1 0) = false := by decide

-- kv_value_3_6_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (1, .word (0 : BitVec 8)) = false := by decide

-- kv_value_3_7_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (2, .loc 0 0) = false := by decide

-- kv_value_4_0_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 1) (0, .word (0 : BitVec 8)) = false := by decide

-- kv_value_4_1_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 1) (0, .word (255 : BitVec 8)) = false := by decide

-- kv_value_4_2_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 1) (0, .word (128 : BitVec 8)) = false := by decide

-- kv_value_4_3_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 1) (0, .loc 0 0) = true := by decide

-- kv_value_4_4_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 1) (0, .loc 0 1) = true := by decide

-- kv_value_4_5_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 1) (0, .loc 1 0) = false := by decide

-- kv_value_4_6_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 1) (1, .word (0 : BitVec 8)) = false := by decide

-- kv_value_4_7_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 1) (2, .loc 0 0) = false := by decide

-- kv_value_5_0_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .word (0 : BitVec 8)) = false := by decide

-- kv_value_5_1_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .word (255 : BitVec 8)) = false := by decide

-- kv_value_5_2_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .word (128 : BitVec 8)) = false := by decide

-- kv_value_5_3_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .loc 0 0) = true := by decide

-- kv_value_5_4_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .loc 0 1) = true := by decide

-- kv_value_5_5_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .loc 1 0) = true := by decide

-- kv_value_5_6_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (1, .word (0 : BitVec 8)) = false := by decide

-- kv_value_5_7_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (2, .loc 0 0) = false := by decide

-- kv_value_6_0_8
example : wordSemKeyValCompare (width := 8) (1, .word (0 : BitVec 8)) (0, .word (0 : BitVec 8)) = true := by decide

-- kv_value_6_1_8
example : wordSemKeyValCompare (width := 8) (1, .word (0 : BitVec 8)) (0, .word (255 : BitVec 8)) = true := by decide

-- kv_value_6_2_8
example : wordSemKeyValCompare (width := 8) (1, .word (0 : BitVec 8)) (0, .word (128 : BitVec 8)) = true := by decide

-- kv_value_6_3_8
example : wordSemKeyValCompare (width := 8) (1, .word (0 : BitVec 8)) (0, .loc 0 0) = true := by decide

-- kv_value_6_4_8
example : wordSemKeyValCompare (width := 8) (1, .word (0 : BitVec 8)) (0, .loc 0 1) = true := by decide

-- kv_value_6_5_8
example : wordSemKeyValCompare (width := 8) (1, .word (0 : BitVec 8)) (0, .loc 1 0) = true := by decide

-- kv_value_6_6_8
example : wordSemKeyValCompare (width := 8) (1, .word (0 : BitVec 8)) (1, .word (0 : BitVec 8)) = true := by decide

-- kv_value_6_7_8
example : wordSemKeyValCompare (width := 8) (1, .word (0 : BitVec 8)) (2, .loc 0 0) = false := by decide

-- kv_value_7_0_8
example : wordSemKeyValCompare (width := 8) (2, .loc 0 0) (0, .word (0 : BitVec 8)) = true := by decide

-- kv_value_7_1_8
example : wordSemKeyValCompare (width := 8) (2, .loc 0 0) (0, .word (255 : BitVec 8)) = true := by decide

-- kv_value_7_2_8
example : wordSemKeyValCompare (width := 8) (2, .loc 0 0) (0, .word (128 : BitVec 8)) = true := by decide

-- kv_value_7_3_8
example : wordSemKeyValCompare (width := 8) (2, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_7_4_8
example : wordSemKeyValCompare (width := 8) (2, .loc 0 0) (0, .loc 0 1) = true := by decide

-- kv_value_7_5_8
example : wordSemKeyValCompare (width := 8) (2, .loc 0 0) (0, .loc 1 0) = true := by decide

-- kv_value_7_6_8
example : wordSemKeyValCompare (width := 8) (2, .loc 0 0) (1, .word (0 : BitVec 8)) = true := by decide

-- kv_value_7_7_8
example : wordSemKeyValCompare (width := 8) (2, .loc 0 0) (2, .loc 0 0) = true := by decide

-- kv_transit_0_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .word (0 : BitVec 8)) = true → wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (0, .word (128 : BitVec 8)) = true → wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .word (128 : BitVec 8)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_1_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .word (0 : BitVec 8)) = true → wordSemKeyValCompare (width := 8) (0, .word (0 : BitVec 8)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

-- kv_transit_2_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .word (0 : BitVec 8)) = true → wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .word (0 : BitVec 8)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_3_8
example : wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_4_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .word (255 : BitVec 8)) = true → wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .word (0 : BitVec 8)) = true → wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .word (0 : BitVec 8)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_5_8
example : wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .word (255 : BitVec 8)) = true → wordSemKeyValCompare (width := 8) (0, .word (255 : BitVec 8)) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 8) (0, .loc 0 0) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_6_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 8) (0, .loc 0 1) (0, .word (0 : BitVec 8)) = true → wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .word (0 : BitVec 8)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_7_8
example : wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 8) (0, .loc 0 1) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 8) (0, .loc 1 0) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

-- kv_value_0_0_64
example : wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (0, .word (0 : BitVec 64)) = true := by decide

-- kv_value_0_1_64
example : wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (0, .word (18446744073709551615 : BitVec 64)) = false := by decide

-- kv_value_0_2_64
example : wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (0, .word (9223372036854775808 : BitVec 64)) = false := by decide

-- kv_value_0_3_64
example : wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (0, .loc 0 0) = true := by decide

-- kv_value_0_4_64
example : wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (0, .loc 0 1) = true := by decide

-- kv_value_0_5_64
example : wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (0, .loc 1 0) = true := by decide

-- kv_value_0_6_64
example : wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (1, .word (0 : BitVec 64)) = false := by decide

-- kv_value_0_7_64
example : wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (2, .loc 0 0) = false := by decide

-- kv_value_1_0_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .word (0 : BitVec 64)) = true := by decide

-- kv_value_1_1_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .word (18446744073709551615 : BitVec 64)) = true := by decide

-- kv_value_1_2_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .word (9223372036854775808 : BitVec 64)) = false := by decide

-- kv_value_1_3_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .loc 0 0) = true := by decide

-- kv_value_1_4_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .loc 0 1) = true := by decide

-- kv_value_1_5_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .loc 1 0) = true := by decide

-- kv_value_1_6_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (1, .word (0 : BitVec 64)) = false := by decide

-- kv_value_1_7_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (2, .loc 0 0) = false := by decide

-- kv_value_2_0_64
example : wordSemKeyValCompare (width := 64) (0, .word (9223372036854775808 : BitVec 64)) (0, .word (0 : BitVec 64)) = true := by decide

-- kv_value_2_1_64
example : wordSemKeyValCompare (width := 64) (0, .word (9223372036854775808 : BitVec 64)) (0, .word (18446744073709551615 : BitVec 64)) = true := by decide

-- kv_value_2_2_64
example : wordSemKeyValCompare (width := 64) (0, .word (9223372036854775808 : BitVec 64)) (0, .word (9223372036854775808 : BitVec 64)) = true := by decide

-- kv_value_2_3_64
example : wordSemKeyValCompare (width := 64) (0, .word (9223372036854775808 : BitVec 64)) (0, .loc 0 0) = true := by decide

-- kv_value_2_4_64
example : wordSemKeyValCompare (width := 64) (0, .word (9223372036854775808 : BitVec 64)) (0, .loc 0 1) = true := by decide

-- kv_value_2_5_64
example : wordSemKeyValCompare (width := 64) (0, .word (9223372036854775808 : BitVec 64)) (0, .loc 1 0) = true := by decide

-- kv_value_2_6_64
example : wordSemKeyValCompare (width := 64) (0, .word (9223372036854775808 : BitVec 64)) (1, .word (0 : BitVec 64)) = false := by decide

-- kv_value_2_7_64
example : wordSemKeyValCompare (width := 64) (0, .word (9223372036854775808 : BitVec 64)) (2, .loc 0 0) = false := by decide

-- kv_value_3_0_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .word (0 : BitVec 64)) = false := by decide

-- kv_value_3_1_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .word (18446744073709551615 : BitVec 64)) = false := by decide

-- kv_value_3_2_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .word (9223372036854775808 : BitVec 64)) = false := by decide

-- kv_value_3_3_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_3_4_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .loc 0 1) = false := by decide

-- kv_value_3_5_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .loc 1 0) = false := by decide

-- kv_value_3_6_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (1, .word (0 : BitVec 64)) = false := by decide

-- kv_value_3_7_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (2, .loc 0 0) = false := by decide

-- kv_value_4_0_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 1) (0, .word (0 : BitVec 64)) = false := by decide

-- kv_value_4_1_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 1) (0, .word (18446744073709551615 : BitVec 64)) = false := by decide

-- kv_value_4_2_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 1) (0, .word (9223372036854775808 : BitVec 64)) = false := by decide

-- kv_value_4_3_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 1) (0, .loc 0 0) = true := by decide

-- kv_value_4_4_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 1) (0, .loc 0 1) = true := by decide

-- kv_value_4_5_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 1) (0, .loc 1 0) = false := by decide

-- kv_value_4_6_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 1) (1, .word (0 : BitVec 64)) = false := by decide

-- kv_value_4_7_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 1) (2, .loc 0 0) = false := by decide

-- kv_value_5_0_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .word (0 : BitVec 64)) = false := by decide

-- kv_value_5_1_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .word (18446744073709551615 : BitVec 64)) = false := by decide

-- kv_value_5_2_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .word (9223372036854775808 : BitVec 64)) = false := by decide

-- kv_value_5_3_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .loc 0 0) = true := by decide

-- kv_value_5_4_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .loc 0 1) = true := by decide

-- kv_value_5_5_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .loc 1 0) = true := by decide

-- kv_value_5_6_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (1, .word (0 : BitVec 64)) = false := by decide

-- kv_value_5_7_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (2, .loc 0 0) = false := by decide

-- kv_value_6_0_64
example : wordSemKeyValCompare (width := 64) (1, .word (0 : BitVec 64)) (0, .word (0 : BitVec 64)) = true := by decide

-- kv_value_6_1_64
example : wordSemKeyValCompare (width := 64) (1, .word (0 : BitVec 64)) (0, .word (18446744073709551615 : BitVec 64)) = true := by decide

-- kv_value_6_2_64
example : wordSemKeyValCompare (width := 64) (1, .word (0 : BitVec 64)) (0, .word (9223372036854775808 : BitVec 64)) = true := by decide

-- kv_value_6_3_64
example : wordSemKeyValCompare (width := 64) (1, .word (0 : BitVec 64)) (0, .loc 0 0) = true := by decide

-- kv_value_6_4_64
example : wordSemKeyValCompare (width := 64) (1, .word (0 : BitVec 64)) (0, .loc 0 1) = true := by decide

-- kv_value_6_5_64
example : wordSemKeyValCompare (width := 64) (1, .word (0 : BitVec 64)) (0, .loc 1 0) = true := by decide

-- kv_value_6_6_64
example : wordSemKeyValCompare (width := 64) (1, .word (0 : BitVec 64)) (1, .word (0 : BitVec 64)) = true := by decide

-- kv_value_6_7_64
example : wordSemKeyValCompare (width := 64) (1, .word (0 : BitVec 64)) (2, .loc 0 0) = false := by decide

-- kv_value_7_0_64
example : wordSemKeyValCompare (width := 64) (2, .loc 0 0) (0, .word (0 : BitVec 64)) = true := by decide

-- kv_value_7_1_64
example : wordSemKeyValCompare (width := 64) (2, .loc 0 0) (0, .word (18446744073709551615 : BitVec 64)) = true := by decide

-- kv_value_7_2_64
example : wordSemKeyValCompare (width := 64) (2, .loc 0 0) (0, .word (9223372036854775808 : BitVec 64)) = true := by decide

-- kv_value_7_3_64
example : wordSemKeyValCompare (width := 64) (2, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_7_4_64
example : wordSemKeyValCompare (width := 64) (2, .loc 0 0) (0, .loc 0 1) = true := by decide

-- kv_value_7_5_64
example : wordSemKeyValCompare (width := 64) (2, .loc 0 0) (0, .loc 1 0) = true := by decide

-- kv_value_7_6_64
example : wordSemKeyValCompare (width := 64) (2, .loc 0 0) (1, .word (0 : BitVec 64)) = true := by decide

-- kv_value_7_7_64
example : wordSemKeyValCompare (width := 64) (2, .loc 0 0) (2, .loc 0 0) = true := by decide

-- kv_transit_0_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .word (0 : BitVec 64)) = true → wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (0, .word (9223372036854775808 : BitVec 64)) = true → wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .word (9223372036854775808 : BitVec 64)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_1_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .word (0 : BitVec 64)) = true → wordSemKeyValCompare (width := 64) (0, .word (0 : BitVec 64)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

-- kv_transit_2_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .word (0 : BitVec 64)) = true → wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .word (0 : BitVec 64)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_3_64
example : wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_4_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .word (18446744073709551615 : BitVec 64)) = true → wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .word (0 : BitVec 64)) = true → wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .word (0 : BitVec 64)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_5_64
example : wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .word (18446744073709551615 : BitVec 64)) = true → wordSemKeyValCompare (width := 64) (0, .word (18446744073709551615 : BitVec 64)) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 64) (0, .loc 0 0) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_6_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 64) (0, .loc 0 1) (0, .word (0 : BitVec 64)) = true → wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .word (0 : BitVec 64)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_7_64
example : wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 64) (0, .loc 0 1) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 64) (0, .loc 1 0) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

-- kv_value_0_0_80
example : wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (0, .word (0 : BitVec 80)) = true := by decide

-- kv_value_0_1_80
example : wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (0, .word (1208925819614629174706175 : BitVec 80)) = false := by decide

-- kv_value_0_2_80
example : wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (0, .word (604462909807314587353088 : BitVec 80)) = false := by decide

-- kv_value_0_3_80
example : wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (0, .loc 0 0) = true := by decide

-- kv_value_0_4_80
example : wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (0, .loc 0 1) = true := by decide

-- kv_value_0_5_80
example : wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (0, .loc 1 0) = true := by decide

-- kv_value_0_6_80
example : wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (1, .word (0 : BitVec 80)) = false := by decide

-- kv_value_0_7_80
example : wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (2, .loc 0 0) = false := by decide

-- kv_value_1_0_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .word (0 : BitVec 80)) = true := by decide

-- kv_value_1_1_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .word (1208925819614629174706175 : BitVec 80)) = true := by decide

-- kv_value_1_2_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .word (604462909807314587353088 : BitVec 80)) = false := by decide

-- kv_value_1_3_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .loc 0 0) = true := by decide

-- kv_value_1_4_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .loc 0 1) = true := by decide

-- kv_value_1_5_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .loc 1 0) = true := by decide

-- kv_value_1_6_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (1, .word (0 : BitVec 80)) = false := by decide

-- kv_value_1_7_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (2, .loc 0 0) = false := by decide

-- kv_value_2_0_80
example : wordSemKeyValCompare (width := 80) (0, .word (604462909807314587353088 : BitVec 80)) (0, .word (0 : BitVec 80)) = true := by decide

-- kv_value_2_1_80
example : wordSemKeyValCompare (width := 80) (0, .word (604462909807314587353088 : BitVec 80)) (0, .word (1208925819614629174706175 : BitVec 80)) = true := by decide

-- kv_value_2_2_80
example : wordSemKeyValCompare (width := 80) (0, .word (604462909807314587353088 : BitVec 80)) (0, .word (604462909807314587353088 : BitVec 80)) = true := by decide

-- kv_value_2_3_80
example : wordSemKeyValCompare (width := 80) (0, .word (604462909807314587353088 : BitVec 80)) (0, .loc 0 0) = true := by decide

-- kv_value_2_4_80
example : wordSemKeyValCompare (width := 80) (0, .word (604462909807314587353088 : BitVec 80)) (0, .loc 0 1) = true := by decide

-- kv_value_2_5_80
example : wordSemKeyValCompare (width := 80) (0, .word (604462909807314587353088 : BitVec 80)) (0, .loc 1 0) = true := by decide

-- kv_value_2_6_80
example : wordSemKeyValCompare (width := 80) (0, .word (604462909807314587353088 : BitVec 80)) (1, .word (0 : BitVec 80)) = false := by decide

-- kv_value_2_7_80
example : wordSemKeyValCompare (width := 80) (0, .word (604462909807314587353088 : BitVec 80)) (2, .loc 0 0) = false := by decide

-- kv_value_3_0_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .word (0 : BitVec 80)) = false := by decide

-- kv_value_3_1_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .word (1208925819614629174706175 : BitVec 80)) = false := by decide

-- kv_value_3_2_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .word (604462909807314587353088 : BitVec 80)) = false := by decide

-- kv_value_3_3_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_3_4_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .loc 0 1) = false := by decide

-- kv_value_3_5_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .loc 1 0) = false := by decide

-- kv_value_3_6_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (1, .word (0 : BitVec 80)) = false := by decide

-- kv_value_3_7_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (2, .loc 0 0) = false := by decide

-- kv_value_4_0_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 1) (0, .word (0 : BitVec 80)) = false := by decide

-- kv_value_4_1_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 1) (0, .word (1208925819614629174706175 : BitVec 80)) = false := by decide

-- kv_value_4_2_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 1) (0, .word (604462909807314587353088 : BitVec 80)) = false := by decide

-- kv_value_4_3_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 1) (0, .loc 0 0) = true := by decide

-- kv_value_4_4_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 1) (0, .loc 0 1) = true := by decide

-- kv_value_4_5_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 1) (0, .loc 1 0) = false := by decide

-- kv_value_4_6_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 1) (1, .word (0 : BitVec 80)) = false := by decide

-- kv_value_4_7_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 1) (2, .loc 0 0) = false := by decide

-- kv_value_5_0_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .word (0 : BitVec 80)) = false := by decide

-- kv_value_5_1_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .word (1208925819614629174706175 : BitVec 80)) = false := by decide

-- kv_value_5_2_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .word (604462909807314587353088 : BitVec 80)) = false := by decide

-- kv_value_5_3_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .loc 0 0) = true := by decide

-- kv_value_5_4_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .loc 0 1) = true := by decide

-- kv_value_5_5_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .loc 1 0) = true := by decide

-- kv_value_5_6_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (1, .word (0 : BitVec 80)) = false := by decide

-- kv_value_5_7_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (2, .loc 0 0) = false := by decide

-- kv_value_6_0_80
example : wordSemKeyValCompare (width := 80) (1, .word (0 : BitVec 80)) (0, .word (0 : BitVec 80)) = true := by decide

-- kv_value_6_1_80
example : wordSemKeyValCompare (width := 80) (1, .word (0 : BitVec 80)) (0, .word (1208925819614629174706175 : BitVec 80)) = true := by decide

-- kv_value_6_2_80
example : wordSemKeyValCompare (width := 80) (1, .word (0 : BitVec 80)) (0, .word (604462909807314587353088 : BitVec 80)) = true := by decide

-- kv_value_6_3_80
example : wordSemKeyValCompare (width := 80) (1, .word (0 : BitVec 80)) (0, .loc 0 0) = true := by decide

-- kv_value_6_4_80
example : wordSemKeyValCompare (width := 80) (1, .word (0 : BitVec 80)) (0, .loc 0 1) = true := by decide

-- kv_value_6_5_80
example : wordSemKeyValCompare (width := 80) (1, .word (0 : BitVec 80)) (0, .loc 1 0) = true := by decide

-- kv_value_6_6_80
example : wordSemKeyValCompare (width := 80) (1, .word (0 : BitVec 80)) (1, .word (0 : BitVec 80)) = true := by decide

-- kv_value_6_7_80
example : wordSemKeyValCompare (width := 80) (1, .word (0 : BitVec 80)) (2, .loc 0 0) = false := by decide

-- kv_value_7_0_80
example : wordSemKeyValCompare (width := 80) (2, .loc 0 0) (0, .word (0 : BitVec 80)) = true := by decide

-- kv_value_7_1_80
example : wordSemKeyValCompare (width := 80) (2, .loc 0 0) (0, .word (1208925819614629174706175 : BitVec 80)) = true := by decide

-- kv_value_7_2_80
example : wordSemKeyValCompare (width := 80) (2, .loc 0 0) (0, .word (604462909807314587353088 : BitVec 80)) = true := by decide

-- kv_value_7_3_80
example : wordSemKeyValCompare (width := 80) (2, .loc 0 0) (0, .loc 0 0) = true := by decide

-- kv_value_7_4_80
example : wordSemKeyValCompare (width := 80) (2, .loc 0 0) (0, .loc 0 1) = true := by decide

-- kv_value_7_5_80
example : wordSemKeyValCompare (width := 80) (2, .loc 0 0) (0, .loc 1 0) = true := by decide

-- kv_value_7_6_80
example : wordSemKeyValCompare (width := 80) (2, .loc 0 0) (1, .word (0 : BitVec 80)) = true := by decide

-- kv_value_7_7_80
example : wordSemKeyValCompare (width := 80) (2, .loc 0 0) (2, .loc 0 0) = true := by decide

-- kv_transit_0_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .word (0 : BitVec 80)) = true → wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (0, .word (604462909807314587353088 : BitVec 80)) = true → wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .word (604462909807314587353088 : BitVec 80)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_1_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .word (0 : BitVec 80)) = true → wordSemKeyValCompare (width := 80) (0, .word (0 : BitVec 80)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

-- kv_transit_2_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .word (0 : BitVec 80)) = true → wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .word (0 : BitVec 80)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_3_80
example : wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_4_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .word (1208925819614629174706175 : BitVec 80)) = true → wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .word (0 : BitVec 80)) = true → wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .word (0 : BitVec 80)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_5_80
example : wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .word (1208925819614629174706175 : BitVec 80)) = true → wordSemKeyValCompare (width := 80) (0, .word (1208925819614629174706175 : BitVec 80)) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 80) (0, .loc 0 0) (0, .loc 0 1) = true := transitiveKeyValCompare _ _ _

-- kv_transit_6_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 80) (0, .loc 0 1) (0, .word (0 : BitVec 80)) = true → wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .word (0 : BitVec 80)) = true := transitiveKeyValCompare _ _ _

-- kv_transit_7_80
example : wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .loc 0 1) = true → wordSemKeyValCompare (width := 80) (0, .loc 0 1) (0, .loc 0 0) = true → wordSemKeyValCompare (width := 80) (0, .loc 1 0) (0, .loc 0 0) = true := transitiveKeyValCompare _ _ _

example {width : Nat} [NeZero width] (x y : Nat × WordLocW width) := totalKeyValCompare x y
example {width : Nat} [NeZero width] (x y z : Nat × WordLocW width) (hxy : wordSemKeyValCompare x y = true) (hyz : wordSemKeyValCompare y z = true) := transitiveKeyValCompare x y z hxy hyz

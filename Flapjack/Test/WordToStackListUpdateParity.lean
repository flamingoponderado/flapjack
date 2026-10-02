import Flapjack.Compiler.Backend.WordToStack.Proofs.ListUpdate
open Flapjack.Compiler.Backend.WordToStack

-- lu_output_0_0_0
example : listUpdate ([] : List Nat) 0 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_0_0_0
example : (listUpdate ([] : List Nat) 0 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([] : List Nat) 0 ([] : List Nat)).take 2 = listUpdate ([] : List Nat) 0 (([] : List Nat).take 2) ∧ (([] : List Nat).length + 0 ≤ 2 → (listUpdate ([] : List Nat) 0 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (0 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 0 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([] : List Nat) 0 ([] : List Nat)).drop 2 = listUpdate ([] : List Nat) (0-2) (([] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 0 ([] : List Nat) = ([] : List Nat).take 0 ++ listUpdate ([] : List Nat) 0 (([] : List Nat).drop 0) := by decide

-- lu_output_0_0_1
example : listUpdate ([] : List Nat) 1 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_0_0_1
example : (listUpdate ([] : List Nat) 1 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([] : List Nat) 1 ([] : List Nat)).take 2 = listUpdate ([] : List Nat) 1 (([] : List Nat).take 2) ∧ (([] : List Nat).length + 1 ≤ 2 → (listUpdate ([] : List Nat) 1 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (1 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 1 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([] : List Nat) 1 ([] : List Nat)).drop 2 = listUpdate ([] : List Nat) (1-2) (([] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 1 ([] : List Nat) = ([] : List Nat).take 1 ++ listUpdate ([] : List Nat) 0 (([] : List Nat).drop 1) := by decide

-- lu_output_0_0_3
example : listUpdate ([] : List Nat) 3 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_0_0_3
example : (listUpdate ([] : List Nat) 3 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([] : List Nat) 3 ([] : List Nat)).take 2 = listUpdate ([] : List Nat) 3 (([] : List Nat).take 2) ∧ (([] : List Nat).length + 3 ≤ 2 → (listUpdate ([] : List Nat) 3 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (3 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 3 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([] : List Nat) 3 ([] : List Nat)).drop 2 = listUpdate ([] : List Nat) (3-2) (([] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 3 ([] : List Nat) = ([] : List Nat).take 3 ++ listUpdate ([] : List Nat) 0 (([] : List Nat).drop 3) := by decide

-- lu_output_0_0_8
example : listUpdate ([] : List Nat) 8 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_0_0_8
example : (listUpdate ([] : List Nat) 8 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([] : List Nat) 8 ([] : List Nat)).take 2 = listUpdate ([] : List Nat) 8 (([] : List Nat).take 2) ∧ (([] : List Nat).length + 8 ≤ 2 → (listUpdate ([] : List Nat) 8 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (8 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 8 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([] : List Nat) 8 ([] : List Nat)).drop 2 = listUpdate ([] : List Nat) (8-2) (([] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 8 ([] : List Nat) = ([] : List Nat).take 8 ++ listUpdate ([] : List Nat) 0 (([] : List Nat).drop 8) := by decide

-- lu_output_0_1_0
example : listUpdate ([] : List Nat) 0 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_0_1_0
example : (listUpdate ([] : List Nat) 0 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([] : List Nat) 0 ([1] : List Nat)).take 2 = listUpdate ([] : List Nat) 0 (([1] : List Nat).take 2) ∧ (([] : List Nat).length + 0 ≤ 2 → (listUpdate ([] : List Nat) 0 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (0 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 0 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([] : List Nat) 0 ([1] : List Nat)).drop 2 = listUpdate ([] : List Nat) (0-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 0 ([1] : List Nat) = ([1] : List Nat).take 0 ++ listUpdate ([] : List Nat) 0 (([1] : List Nat).drop 0) := by decide

-- lu_output_0_1_1
example : listUpdate ([] : List Nat) 1 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_0_1_1
example : (listUpdate ([] : List Nat) 1 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([] : List Nat) 1 ([1] : List Nat)).take 2 = listUpdate ([] : List Nat) 1 (([1] : List Nat).take 2) ∧ (([] : List Nat).length + 1 ≤ 2 → (listUpdate ([] : List Nat) 1 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (1 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 1 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([] : List Nat) 1 ([1] : List Nat)).drop 2 = listUpdate ([] : List Nat) (1-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 1 ([1] : List Nat) = ([1] : List Nat).take 1 ++ listUpdate ([] : List Nat) 0 (([1] : List Nat).drop 1) := by decide

-- lu_output_0_1_3
example : listUpdate ([] : List Nat) 3 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_0_1_3
example : (listUpdate ([] : List Nat) 3 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([] : List Nat) 3 ([1] : List Nat)).take 2 = listUpdate ([] : List Nat) 3 (([1] : List Nat).take 2) ∧ (([] : List Nat).length + 3 ≤ 2 → (listUpdate ([] : List Nat) 3 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (3 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 3 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([] : List Nat) 3 ([1] : List Nat)).drop 2 = listUpdate ([] : List Nat) (3-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 3 ([1] : List Nat) = ([1] : List Nat).take 3 ++ listUpdate ([] : List Nat) 0 (([1] : List Nat).drop 3) := by decide

-- lu_output_0_1_8
example : listUpdate ([] : List Nat) 8 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_0_1_8
example : (listUpdate ([] : List Nat) 8 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([] : List Nat) 8 ([1] : List Nat)).take 2 = listUpdate ([] : List Nat) 8 (([1] : List Nat).take 2) ∧ (([] : List Nat).length + 8 ≤ 2 → (listUpdate ([] : List Nat) 8 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (8 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 8 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([] : List Nat) 8 ([1] : List Nat)).drop 2 = listUpdate ([] : List Nat) (8-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 8 ([1] : List Nat) = ([1] : List Nat).take 8 ++ listUpdate ([] : List Nat) 0 (([1] : List Nat).drop 8) := by decide

-- lu_output_0_2_0
example : listUpdate ([] : List Nat) 0 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_0_2_0
example : (listUpdate ([] : List Nat) 0 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([] : List Nat) 0 ([2, 4] : List Nat)).take 2 = listUpdate ([] : List Nat) 0 (([2, 4] : List Nat).take 2) ∧ (([] : List Nat).length + 0 ≤ 2 → (listUpdate ([] : List Nat) 0 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (0 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 0 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([] : List Nat) 0 ([2, 4] : List Nat)).drop 2 = listUpdate ([] : List Nat) (0-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 0 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 0 ++ listUpdate ([] : List Nat) 0 (([2, 4] : List Nat).drop 0) := by decide

-- lu_output_0_2_1
example : listUpdate ([] : List Nat) 1 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_0_2_1
example : (listUpdate ([] : List Nat) 1 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([] : List Nat) 1 ([2, 4] : List Nat)).take 2 = listUpdate ([] : List Nat) 1 (([2, 4] : List Nat).take 2) ∧ (([] : List Nat).length + 1 ≤ 2 → (listUpdate ([] : List Nat) 1 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (1 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 1 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([] : List Nat) 1 ([2, 4] : List Nat)).drop 2 = listUpdate ([] : List Nat) (1-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 1 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 1 ++ listUpdate ([] : List Nat) 0 (([2, 4] : List Nat).drop 1) := by decide

-- lu_output_0_2_3
example : listUpdate ([] : List Nat) 3 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_0_2_3
example : (listUpdate ([] : List Nat) 3 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([] : List Nat) 3 ([2, 4] : List Nat)).take 2 = listUpdate ([] : List Nat) 3 (([2, 4] : List Nat).take 2) ∧ (([] : List Nat).length + 3 ≤ 2 → (listUpdate ([] : List Nat) 3 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (3 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 3 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([] : List Nat) 3 ([2, 4] : List Nat)).drop 2 = listUpdate ([] : List Nat) (3-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 3 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 3 ++ listUpdate ([] : List Nat) 0 (([2, 4] : List Nat).drop 3) := by decide

-- lu_output_0_2_8
example : listUpdate ([] : List Nat) 8 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_0_2_8
example : (listUpdate ([] : List Nat) 8 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([] : List Nat) 8 ([2, 4] : List Nat)).take 2 = listUpdate ([] : List Nat) 8 (([2, 4] : List Nat).take 2) ∧ (([] : List Nat).length + 8 ≤ 2 → (listUpdate ([] : List Nat) 8 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (8 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 8 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([] : List Nat) 8 ([2, 4] : List Nat)).drop 2 = listUpdate ([] : List Nat) (8-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 8 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 8 ++ listUpdate ([] : List Nat) 0 (([2, 4] : List Nat).drop 8) := by decide

-- lu_output_0_3_0
example : listUpdate ([] : List Nat) 0 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_0_3_0
example : (listUpdate ([] : List Nat) 0 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([] : List Nat) 0 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([] : List Nat) 0 (([8, 6, 4] : List Nat).take 2) ∧ (([] : List Nat).length + 0 ≤ 2 → (listUpdate ([] : List Nat) 0 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (0 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 0 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([] : List Nat) 0 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([] : List Nat) (0-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 0 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 0 ++ listUpdate ([] : List Nat) 0 (([8, 6, 4] : List Nat).drop 0) := by decide

-- lu_output_0_3_1
example : listUpdate ([] : List Nat) 1 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_0_3_1
example : (listUpdate ([] : List Nat) 1 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([] : List Nat) 1 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([] : List Nat) 1 (([8, 6, 4] : List Nat).take 2) ∧ (([] : List Nat).length + 1 ≤ 2 → (listUpdate ([] : List Nat) 1 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (1 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 1 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([] : List Nat) 1 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([] : List Nat) (1-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 1 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 1 ++ listUpdate ([] : List Nat) 0 (([8, 6, 4] : List Nat).drop 1) := by decide

-- lu_output_0_3_3
example : listUpdate ([] : List Nat) 3 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_0_3_3
example : (listUpdate ([] : List Nat) 3 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([] : List Nat) 3 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([] : List Nat) 3 (([8, 6, 4] : List Nat).take 2) ∧ (([] : List Nat).length + 3 ≤ 2 → (listUpdate ([] : List Nat) 3 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (3 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 3 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([] : List Nat) 3 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([] : List Nat) (3-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 3 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 3 ++ listUpdate ([] : List Nat) 0 (([8, 6, 4] : List Nat).drop 3) := by decide

-- lu_output_0_3_8
example : listUpdate ([] : List Nat) 8 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_0_3_8
example : (listUpdate ([] : List Nat) 8 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([] : List Nat) 8 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([] : List Nat) 8 (([8, 6, 4] : List Nat).take 2) ∧ (([] : List Nat).length + 8 ≤ 2 → (listUpdate ([] : List Nat) 8 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (8 + ([] : List Nat).length ≤ 2 → (listUpdate ([] : List Nat) 8 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([] : List Nat) 8 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([] : List Nat) (8-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([] : List Nat) 8 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 8 ++ listUpdate ([] : List Nat) 0 (([8, 6, 4] : List Nat).drop 8) := by decide

-- lu_output_1_0_0
example : listUpdate ([1] : List Nat) 0 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_1_0_0
example : (listUpdate ([1] : List Nat) 0 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([1] : List Nat) 0 ([] : List Nat)).take 2 = listUpdate ([1] : List Nat) 0 (([] : List Nat).take 2) ∧ (([1] : List Nat).length + 0 ≤ 2 → (listUpdate ([1] : List Nat) 0 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (0 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 0 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([1] : List Nat) 0 ([] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (0-2) (([] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 0 ([] : List Nat) = ([] : List Nat).take 0 ++ listUpdate ([1] : List Nat) 0 (([] : List Nat).drop 0) := by decide

-- lu_output_1_0_1
example : listUpdate ([1] : List Nat) 1 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_1_0_1
example : (listUpdate ([1] : List Nat) 1 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([1] : List Nat) 1 ([] : List Nat)).take 2 = listUpdate ([1] : List Nat) 1 (([] : List Nat).take 2) ∧ (([1] : List Nat).length + 1 ≤ 2 → (listUpdate ([1] : List Nat) 1 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (1 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 1 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([1] : List Nat) 1 ([] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (1-2) (([] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 1 ([] : List Nat) = ([] : List Nat).take 1 ++ listUpdate ([1] : List Nat) 0 (([] : List Nat).drop 1) := by decide

-- lu_output_1_0_3
example : listUpdate ([1] : List Nat) 3 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_1_0_3
example : (listUpdate ([1] : List Nat) 3 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([1] : List Nat) 3 ([] : List Nat)).take 2 = listUpdate ([1] : List Nat) 3 (([] : List Nat).take 2) ∧ (([1] : List Nat).length + 3 ≤ 2 → (listUpdate ([1] : List Nat) 3 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (3 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 3 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([1] : List Nat) 3 ([] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (3-2) (([] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 3 ([] : List Nat) = ([] : List Nat).take 3 ++ listUpdate ([1] : List Nat) 0 (([] : List Nat).drop 3) := by decide

-- lu_output_1_0_8
example : listUpdate ([1] : List Nat) 8 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_1_0_8
example : (listUpdate ([1] : List Nat) 8 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([1] : List Nat) 8 ([] : List Nat)).take 2 = listUpdate ([1] : List Nat) 8 (([] : List Nat).take 2) ∧ (([1] : List Nat).length + 8 ≤ 2 → (listUpdate ([1] : List Nat) 8 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (8 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 8 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([1] : List Nat) 8 ([] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (8-2) (([] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 8 ([] : List Nat) = ([] : List Nat).take 8 ++ listUpdate ([1] : List Nat) 0 (([] : List Nat).drop 8) := by decide

-- lu_output_1_1_0
example : listUpdate ([1] : List Nat) 0 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_1_1_0
example : (listUpdate ([1] : List Nat) 0 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([1] : List Nat) 0 ([1] : List Nat)).take 2 = listUpdate ([1] : List Nat) 0 (([1] : List Nat).take 2) ∧ (([1] : List Nat).length + 0 ≤ 2 → (listUpdate ([1] : List Nat) 0 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (0 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 0 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([1] : List Nat) 0 ([1] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (0-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 0 ([1] : List Nat) = ([1] : List Nat).take 0 ++ listUpdate ([1] : List Nat) 0 (([1] : List Nat).drop 0) := by decide

-- lu_output_1_1_1
example : listUpdate ([1] : List Nat) 1 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_1_1_1
example : (listUpdate ([1] : List Nat) 1 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([1] : List Nat) 1 ([1] : List Nat)).take 2 = listUpdate ([1] : List Nat) 1 (([1] : List Nat).take 2) ∧ (([1] : List Nat).length + 1 ≤ 2 → (listUpdate ([1] : List Nat) 1 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (1 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 1 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([1] : List Nat) 1 ([1] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (1-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 1 ([1] : List Nat) = ([1] : List Nat).take 1 ++ listUpdate ([1] : List Nat) 0 (([1] : List Nat).drop 1) := by decide

-- lu_output_1_1_3
example : listUpdate ([1] : List Nat) 3 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_1_1_3
example : (listUpdate ([1] : List Nat) 3 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([1] : List Nat) 3 ([1] : List Nat)).take 2 = listUpdate ([1] : List Nat) 3 (([1] : List Nat).take 2) ∧ (([1] : List Nat).length + 3 ≤ 2 → (listUpdate ([1] : List Nat) 3 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (3 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 3 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([1] : List Nat) 3 ([1] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (3-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 3 ([1] : List Nat) = ([1] : List Nat).take 3 ++ listUpdate ([1] : List Nat) 0 (([1] : List Nat).drop 3) := by decide

-- lu_output_1_1_8
example : listUpdate ([1] : List Nat) 8 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_1_1_8
example : (listUpdate ([1] : List Nat) 8 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([1] : List Nat) 8 ([1] : List Nat)).take 2 = listUpdate ([1] : List Nat) 8 (([1] : List Nat).take 2) ∧ (([1] : List Nat).length + 8 ≤ 2 → (listUpdate ([1] : List Nat) 8 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (8 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 8 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([1] : List Nat) 8 ([1] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (8-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 8 ([1] : List Nat) = ([1] : List Nat).take 8 ++ listUpdate ([1] : List Nat) 0 (([1] : List Nat).drop 8) := by decide

-- lu_output_1_2_0
example : listUpdate ([1] : List Nat) 0 ([2, 4] : List Nat) = ([1, 4] : List Nat) := by decide

-- lu_laws_1_2_0
example : (listUpdate ([1] : List Nat) 0 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([1] : List Nat) 0 ([2, 4] : List Nat)).take 2 = listUpdate ([1] : List Nat) 0 (([2, 4] : List Nat).take 2) ∧ (([1] : List Nat).length + 0 ≤ 2 → (listUpdate ([1] : List Nat) 0 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (0 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 0 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([1] : List Nat) 0 ([2, 4] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (0-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 0 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 0 ++ listUpdate ([1] : List Nat) 0 (([2, 4] : List Nat).drop 0) := by decide

-- lu_output_1_2_1
example : listUpdate ([1] : List Nat) 1 ([2, 4] : List Nat) = ([2, 1] : List Nat) := by decide

-- lu_laws_1_2_1
example : (listUpdate ([1] : List Nat) 1 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([1] : List Nat) 1 ([2, 4] : List Nat)).take 2 = listUpdate ([1] : List Nat) 1 (([2, 4] : List Nat).take 2) ∧ (([1] : List Nat).length + 1 ≤ 2 → (listUpdate ([1] : List Nat) 1 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (1 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 1 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([1] : List Nat) 1 ([2, 4] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (1-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 1 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 1 ++ listUpdate ([1] : List Nat) 0 (([2, 4] : List Nat).drop 1) := by decide

-- lu_output_1_2_3
example : listUpdate ([1] : List Nat) 3 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_1_2_3
example : (listUpdate ([1] : List Nat) 3 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([1] : List Nat) 3 ([2, 4] : List Nat)).take 2 = listUpdate ([1] : List Nat) 3 (([2, 4] : List Nat).take 2) ∧ (([1] : List Nat).length + 3 ≤ 2 → (listUpdate ([1] : List Nat) 3 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (3 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 3 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([1] : List Nat) 3 ([2, 4] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (3-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 3 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 3 ++ listUpdate ([1] : List Nat) 0 (([2, 4] : List Nat).drop 3) := by decide

-- lu_output_1_2_8
example : listUpdate ([1] : List Nat) 8 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_1_2_8
example : (listUpdate ([1] : List Nat) 8 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([1] : List Nat) 8 ([2, 4] : List Nat)).take 2 = listUpdate ([1] : List Nat) 8 (([2, 4] : List Nat).take 2) ∧ (([1] : List Nat).length + 8 ≤ 2 → (listUpdate ([1] : List Nat) 8 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (8 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 8 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([1] : List Nat) 8 ([2, 4] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (8-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 8 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 8 ++ listUpdate ([1] : List Nat) 0 (([2, 4] : List Nat).drop 8) := by decide

-- lu_output_1_3_0
example : listUpdate ([1] : List Nat) 0 ([8, 6, 4] : List Nat) = ([1, 6, 4] : List Nat) := by decide

-- lu_laws_1_3_0
example : (listUpdate ([1] : List Nat) 0 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([1] : List Nat) 0 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([1] : List Nat) 0 (([8, 6, 4] : List Nat).take 2) ∧ (([1] : List Nat).length + 0 ≤ 2 → (listUpdate ([1] : List Nat) 0 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (0 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 0 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([1] : List Nat) 0 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (0-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 0 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 0 ++ listUpdate ([1] : List Nat) 0 (([8, 6, 4] : List Nat).drop 0) := by decide

-- lu_output_1_3_1
example : listUpdate ([1] : List Nat) 1 ([8, 6, 4] : List Nat) = ([8, 1, 4] : List Nat) := by decide

-- lu_laws_1_3_1
example : (listUpdate ([1] : List Nat) 1 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([1] : List Nat) 1 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([1] : List Nat) 1 (([8, 6, 4] : List Nat).take 2) ∧ (([1] : List Nat).length + 1 ≤ 2 → (listUpdate ([1] : List Nat) 1 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (1 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 1 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([1] : List Nat) 1 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (1-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 1 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 1 ++ listUpdate ([1] : List Nat) 0 (([8, 6, 4] : List Nat).drop 1) := by decide

-- lu_output_1_3_3
example : listUpdate ([1] : List Nat) 3 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_1_3_3
example : (listUpdate ([1] : List Nat) 3 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([1] : List Nat) 3 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([1] : List Nat) 3 (([8, 6, 4] : List Nat).take 2) ∧ (([1] : List Nat).length + 3 ≤ 2 → (listUpdate ([1] : List Nat) 3 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (3 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 3 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([1] : List Nat) 3 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (3-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 3 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 3 ++ listUpdate ([1] : List Nat) 0 (([8, 6, 4] : List Nat).drop 3) := by decide

-- lu_output_1_3_8
example : listUpdate ([1] : List Nat) 8 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_1_3_8
example : (listUpdate ([1] : List Nat) 8 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([1] : List Nat) 8 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([1] : List Nat) 8 (([8, 6, 4] : List Nat).take 2) ∧ (([1] : List Nat).length + 8 ≤ 2 → (listUpdate ([1] : List Nat) 8 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (8 + ([1] : List Nat).length ≤ 2 → (listUpdate ([1] : List Nat) 8 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([1] : List Nat) 8 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([1] : List Nat) (8-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([1] : List Nat) 8 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 8 ++ listUpdate ([1] : List Nat) 0 (([8, 6, 4] : List Nat).drop 8) := by decide

-- lu_output_2_0_0
example : listUpdate ([2, 4] : List Nat) 0 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_2_0_0
example : (listUpdate ([2, 4] : List Nat) 0 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 0 ([] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 0 (([] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 0 ≤ 2 → (listUpdate ([2, 4] : List Nat) 0 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (0 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 0 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([2, 4] : List Nat) 0 ([] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (0-2) (([] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 0 ([] : List Nat) = ([] : List Nat).take 0 ++ listUpdate ([2, 4] : List Nat) 0 (([] : List Nat).drop 0) := by decide

-- lu_output_2_0_1
example : listUpdate ([2, 4] : List Nat) 1 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_2_0_1
example : (listUpdate ([2, 4] : List Nat) 1 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 1 ([] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 1 (([] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 1 ≤ 2 → (listUpdate ([2, 4] : List Nat) 1 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (1 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 1 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([2, 4] : List Nat) 1 ([] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (1-2) (([] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 1 ([] : List Nat) = ([] : List Nat).take 1 ++ listUpdate ([2, 4] : List Nat) 0 (([] : List Nat).drop 1) := by decide

-- lu_output_2_0_3
example : listUpdate ([2, 4] : List Nat) 3 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_2_0_3
example : (listUpdate ([2, 4] : List Nat) 3 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 3 ([] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 3 (([] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 3 ≤ 2 → (listUpdate ([2, 4] : List Nat) 3 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (3 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 3 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([2, 4] : List Nat) 3 ([] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (3-2) (([] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 3 ([] : List Nat) = ([] : List Nat).take 3 ++ listUpdate ([2, 4] : List Nat) 0 (([] : List Nat).drop 3) := by decide

-- lu_output_2_0_8
example : listUpdate ([2, 4] : List Nat) 8 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_2_0_8
example : (listUpdate ([2, 4] : List Nat) 8 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 8 ([] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 8 (([] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 8 ≤ 2 → (listUpdate ([2, 4] : List Nat) 8 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (8 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 8 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([2, 4] : List Nat) 8 ([] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (8-2) (([] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 8 ([] : List Nat) = ([] : List Nat).take 8 ++ listUpdate ([2, 4] : List Nat) 0 (([] : List Nat).drop 8) := by decide

-- lu_output_2_1_0
example : listUpdate ([2, 4] : List Nat) 0 ([1] : List Nat) = ([2] : List Nat) := by decide

-- lu_laws_2_1_0
example : (listUpdate ([2, 4] : List Nat) 0 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 0 ([1] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 0 (([1] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 0 ≤ 2 → (listUpdate ([2, 4] : List Nat) 0 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (0 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 0 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([2, 4] : List Nat) 0 ([1] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (0-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 0 ([1] : List Nat) = ([1] : List Nat).take 0 ++ listUpdate ([2, 4] : List Nat) 0 (([1] : List Nat).drop 0) := by decide

-- lu_output_2_1_1
example : listUpdate ([2, 4] : List Nat) 1 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_2_1_1
example : (listUpdate ([2, 4] : List Nat) 1 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 1 ([1] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 1 (([1] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 1 ≤ 2 → (listUpdate ([2, 4] : List Nat) 1 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (1 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 1 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([2, 4] : List Nat) 1 ([1] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (1-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 1 ([1] : List Nat) = ([1] : List Nat).take 1 ++ listUpdate ([2, 4] : List Nat) 0 (([1] : List Nat).drop 1) := by decide

-- lu_output_2_1_3
example : listUpdate ([2, 4] : List Nat) 3 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_2_1_3
example : (listUpdate ([2, 4] : List Nat) 3 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 3 ([1] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 3 (([1] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 3 ≤ 2 → (listUpdate ([2, 4] : List Nat) 3 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (3 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 3 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([2, 4] : List Nat) 3 ([1] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (3-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 3 ([1] : List Nat) = ([1] : List Nat).take 3 ++ listUpdate ([2, 4] : List Nat) 0 (([1] : List Nat).drop 3) := by decide

-- lu_output_2_1_8
example : listUpdate ([2, 4] : List Nat) 8 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_2_1_8
example : (listUpdate ([2, 4] : List Nat) 8 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 8 ([1] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 8 (([1] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 8 ≤ 2 → (listUpdate ([2, 4] : List Nat) 8 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (8 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 8 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([2, 4] : List Nat) 8 ([1] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (8-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 8 ([1] : List Nat) = ([1] : List Nat).take 8 ++ listUpdate ([2, 4] : List Nat) 0 (([1] : List Nat).drop 8) := by decide

-- lu_output_2_2_0
example : listUpdate ([2, 4] : List Nat) 0 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_2_2_0
example : (listUpdate ([2, 4] : List Nat) 0 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 0 ([2, 4] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 0 (([2, 4] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 0 ≤ 2 → (listUpdate ([2, 4] : List Nat) 0 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (0 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 0 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([2, 4] : List Nat) 0 ([2, 4] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (0-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 0 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 0 ++ listUpdate ([2, 4] : List Nat) 0 (([2, 4] : List Nat).drop 0) := by decide

-- lu_output_2_2_1
example : listUpdate ([2, 4] : List Nat) 1 ([2, 4] : List Nat) = ([2, 2] : List Nat) := by decide

-- lu_laws_2_2_1
example : (listUpdate ([2, 4] : List Nat) 1 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 1 ([2, 4] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 1 (([2, 4] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 1 ≤ 2 → (listUpdate ([2, 4] : List Nat) 1 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (1 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 1 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([2, 4] : List Nat) 1 ([2, 4] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (1-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 1 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 1 ++ listUpdate ([2, 4] : List Nat) 0 (([2, 4] : List Nat).drop 1) := by decide

-- lu_output_2_2_3
example : listUpdate ([2, 4] : List Nat) 3 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_2_2_3
example : (listUpdate ([2, 4] : List Nat) 3 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 3 ([2, 4] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 3 (([2, 4] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 3 ≤ 2 → (listUpdate ([2, 4] : List Nat) 3 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (3 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 3 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([2, 4] : List Nat) 3 ([2, 4] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (3-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 3 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 3 ++ listUpdate ([2, 4] : List Nat) 0 (([2, 4] : List Nat).drop 3) := by decide

-- lu_output_2_2_8
example : listUpdate ([2, 4] : List Nat) 8 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_2_2_8
example : (listUpdate ([2, 4] : List Nat) 8 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 8 ([2, 4] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 8 (([2, 4] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 8 ≤ 2 → (listUpdate ([2, 4] : List Nat) 8 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (8 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 8 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([2, 4] : List Nat) 8 ([2, 4] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (8-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 8 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 8 ++ listUpdate ([2, 4] : List Nat) 0 (([2, 4] : List Nat).drop 8) := by decide

-- lu_output_2_3_0
example : listUpdate ([2, 4] : List Nat) 0 ([8, 6, 4] : List Nat) = ([2, 4, 4] : List Nat) := by decide

-- lu_laws_2_3_0
example : (listUpdate ([2, 4] : List Nat) 0 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 0 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 0 (([8, 6, 4] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 0 ≤ 2 → (listUpdate ([2, 4] : List Nat) 0 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (0 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 0 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([2, 4] : List Nat) 0 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (0-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 0 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 0 ++ listUpdate ([2, 4] : List Nat) 0 (([8, 6, 4] : List Nat).drop 0) := by decide

-- lu_output_2_3_1
example : listUpdate ([2, 4] : List Nat) 1 ([8, 6, 4] : List Nat) = ([8, 2, 4] : List Nat) := by decide

-- lu_laws_2_3_1
example : (listUpdate ([2, 4] : List Nat) 1 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 1 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 1 (([8, 6, 4] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 1 ≤ 2 → (listUpdate ([2, 4] : List Nat) 1 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (1 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 1 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([2, 4] : List Nat) 1 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (1-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 1 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 1 ++ listUpdate ([2, 4] : List Nat) 0 (([8, 6, 4] : List Nat).drop 1) := by decide

-- lu_output_2_3_3
example : listUpdate ([2, 4] : List Nat) 3 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_2_3_3
example : (listUpdate ([2, 4] : List Nat) 3 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 3 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 3 (([8, 6, 4] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 3 ≤ 2 → (listUpdate ([2, 4] : List Nat) 3 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (3 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 3 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([2, 4] : List Nat) 3 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (3-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 3 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 3 ++ listUpdate ([2, 4] : List Nat) 0 (([8, 6, 4] : List Nat).drop 3) := by decide

-- lu_output_2_3_8
example : listUpdate ([2, 4] : List Nat) 8 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_2_3_8
example : (listUpdate ([2, 4] : List Nat) 8 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([2, 4] : List Nat) 8 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([2, 4] : List Nat) 8 (([8, 6, 4] : List Nat).take 2) ∧ (([2, 4] : List Nat).length + 8 ≤ 2 → (listUpdate ([2, 4] : List Nat) 8 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (8 + ([2, 4] : List Nat).length ≤ 2 → (listUpdate ([2, 4] : List Nat) 8 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([2, 4] : List Nat) 8 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([2, 4] : List Nat) (8-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([2, 4] : List Nat) 8 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 8 ++ listUpdate ([2, 4] : List Nat) 0 (([8, 6, 4] : List Nat).drop 8) := by decide

-- lu_output_3_0_0
example : listUpdate ([8, 6, 4] : List Nat) 0 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_3_0_0
example : (listUpdate ([8, 6, 4] : List Nat) 0 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 0 ([] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 0 (([] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 0 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 0 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (0 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 0 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([8, 6, 4] : List Nat) 0 ([] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (0-2) (([] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 0 ([] : List Nat) = ([] : List Nat).take 0 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([] : List Nat).drop 0) := by decide

-- lu_output_3_0_1
example : listUpdate ([8, 6, 4] : List Nat) 1 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_3_0_1
example : (listUpdate ([8, 6, 4] : List Nat) 1 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 1 ([] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 1 (([] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 1 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 1 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (1 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 1 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([8, 6, 4] : List Nat) 1 ([] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (1-2) (([] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 1 ([] : List Nat) = ([] : List Nat).take 1 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([] : List Nat).drop 1) := by decide

-- lu_output_3_0_3
example : listUpdate ([8, 6, 4] : List Nat) 3 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_3_0_3
example : (listUpdate ([8, 6, 4] : List Nat) 3 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 3 ([] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 3 (([] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 3 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 3 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (3 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 3 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([8, 6, 4] : List Nat) 3 ([] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (3-2) (([] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 3 ([] : List Nat) = ([] : List Nat).take 3 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([] : List Nat).drop 3) := by decide

-- lu_output_3_0_8
example : listUpdate ([8, 6, 4] : List Nat) 8 ([] : List Nat) = ([] : List Nat) := by decide

-- lu_laws_3_0_8
example : (listUpdate ([8, 6, 4] : List Nat) 8 ([] : List Nat)).length = ([] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 8 ([] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 8 (([] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 8 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 8 ([] : List Nat)).drop 2 = ([] : List Nat).drop 2) ∧ (8 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 8 ([] : List Nat))[2]? = ([] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([8, 6, 4] : List Nat) 8 ([] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (8-2) (([] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 8 ([] : List Nat) = ([] : List Nat).take 8 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([] : List Nat).drop 8) := by decide

-- lu_output_3_1_0
example : listUpdate ([8, 6, 4] : List Nat) 0 ([1] : List Nat) = ([8] : List Nat) := by decide

-- lu_laws_3_1_0
example : (listUpdate ([8, 6, 4] : List Nat) 0 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 0 ([1] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 0 (([1] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 0 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 0 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (0 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 0 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([8, 6, 4] : List Nat) 0 ([1] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (0-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 0 ([1] : List Nat) = ([1] : List Nat).take 0 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([1] : List Nat).drop 0) := by decide

-- lu_output_3_1_1
example : listUpdate ([8, 6, 4] : List Nat) 1 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_3_1_1
example : (listUpdate ([8, 6, 4] : List Nat) 1 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 1 ([1] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 1 (([1] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 1 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 1 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (1 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 1 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([8, 6, 4] : List Nat) 1 ([1] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (1-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 1 ([1] : List Nat) = ([1] : List Nat).take 1 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([1] : List Nat).drop 1) := by decide

-- lu_output_3_1_3
example : listUpdate ([8, 6, 4] : List Nat) 3 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_3_1_3
example : (listUpdate ([8, 6, 4] : List Nat) 3 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 3 ([1] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 3 (([1] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 3 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 3 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (3 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 3 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([8, 6, 4] : List Nat) 3 ([1] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (3-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 3 ([1] : List Nat) = ([1] : List Nat).take 3 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([1] : List Nat).drop 3) := by decide

-- lu_output_3_1_8
example : listUpdate ([8, 6, 4] : List Nat) 8 ([1] : List Nat) = ([1] : List Nat) := by decide

-- lu_laws_3_1_8
example : (listUpdate ([8, 6, 4] : List Nat) 8 ([1] : List Nat)).length = ([1] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 8 ([1] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 8 (([1] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 8 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 8 ([1] : List Nat)).drop 2 = ([1] : List Nat).drop 2) ∧ (8 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 8 ([1] : List Nat))[2]? = ([1] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([8, 6, 4] : List Nat) 8 ([1] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (8-2) (([1] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 8 ([1] : List Nat) = ([1] : List Nat).take 8 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([1] : List Nat).drop 8) := by decide

-- lu_output_3_2_0
example : listUpdate ([8, 6, 4] : List Nat) 0 ([2, 4] : List Nat) = ([8, 6] : List Nat) := by decide

-- lu_laws_3_2_0
example : (listUpdate ([8, 6, 4] : List Nat) 0 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 0 ([2, 4] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 0 (([2, 4] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 0 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 0 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (0 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 0 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([8, 6, 4] : List Nat) 0 ([2, 4] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (0-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 0 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 0 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([2, 4] : List Nat).drop 0) := by decide

-- lu_output_3_2_1
example : listUpdate ([8, 6, 4] : List Nat) 1 ([2, 4] : List Nat) = ([2, 8] : List Nat) := by decide

-- lu_laws_3_2_1
example : (listUpdate ([8, 6, 4] : List Nat) 1 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 1 ([2, 4] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 1 (([2, 4] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 1 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 1 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (1 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 1 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([8, 6, 4] : List Nat) 1 ([2, 4] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (1-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 1 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 1 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([2, 4] : List Nat).drop 1) := by decide

-- lu_output_3_2_3
example : listUpdate ([8, 6, 4] : List Nat) 3 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_3_2_3
example : (listUpdate ([8, 6, 4] : List Nat) 3 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 3 ([2, 4] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 3 (([2, 4] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 3 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 3 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (3 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 3 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([8, 6, 4] : List Nat) 3 ([2, 4] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (3-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 3 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 3 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([2, 4] : List Nat).drop 3) := by decide

-- lu_output_3_2_8
example : listUpdate ([8, 6, 4] : List Nat) 8 ([2, 4] : List Nat) = ([2, 4] : List Nat) := by decide

-- lu_laws_3_2_8
example : (listUpdate ([8, 6, 4] : List Nat) 8 ([2, 4] : List Nat)).length = ([2, 4] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 8 ([2, 4] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 8 (([2, 4] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 8 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 8 ([2, 4] : List Nat)).drop 2 = ([2, 4] : List Nat).drop 2) ∧ (8 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 8 ([2, 4] : List Nat))[2]? = ([2, 4] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([8, 6, 4] : List Nat) 8 ([2, 4] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (8-2) (([2, 4] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 8 ([2, 4] : List Nat) = ([2, 4] : List Nat).take 8 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([2, 4] : List Nat).drop 8) := by decide

-- lu_output_3_3_0
example : listUpdate ([8, 6, 4] : List Nat) 0 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_3_3_0
example : (listUpdate ([8, 6, 4] : List Nat) 0 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 0 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 0 (([8, 6, 4] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 0 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 0 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (0 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 0 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 0 → (listUpdate ([8, 6, 4] : List Nat) 0 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (0-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 0 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 0 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([8, 6, 4] : List Nat).drop 0) := by decide

-- lu_output_3_3_1
example : listUpdate ([8, 6, 4] : List Nat) 1 ([8, 6, 4] : List Nat) = ([8, 8, 6] : List Nat) := by decide

-- lu_laws_3_3_1
example : (listUpdate ([8, 6, 4] : List Nat) 1 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 1 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 1 (([8, 6, 4] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 1 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 1 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (1 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 1 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 1 → (listUpdate ([8, 6, 4] : List Nat) 1 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (1-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 1 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 1 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([8, 6, 4] : List Nat).drop 1) := by decide

-- lu_output_3_3_3
example : listUpdate ([8, 6, 4] : List Nat) 3 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_3_3_3
example : (listUpdate ([8, 6, 4] : List Nat) 3 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 3 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 3 (([8, 6, 4] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 3 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 3 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (3 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 3 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 3 → (listUpdate ([8, 6, 4] : List Nat) 3 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (3-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 3 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 3 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([8, 6, 4] : List Nat).drop 3) := by decide

-- lu_output_3_3_8
example : listUpdate ([8, 6, 4] : List Nat) 8 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat) := by decide

-- lu_laws_3_3_8
example : (listUpdate ([8, 6, 4] : List Nat) 8 ([8, 6, 4] : List Nat)).length = ([8, 6, 4] : List Nat).length ∧ (listUpdate ([8, 6, 4] : List Nat) 8 ([8, 6, 4] : List Nat)).take 2 = listUpdate ([8, 6, 4] : List Nat) 8 (([8, 6, 4] : List Nat).take 2) ∧ (([8, 6, 4] : List Nat).length + 8 ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 8 ([8, 6, 4] : List Nat)).drop 2 = ([8, 6, 4] : List Nat).drop 2) ∧ (8 + ([8, 6, 4] : List Nat).length ≤ 2 → (listUpdate ([8, 6, 4] : List Nat) 8 ([8, 6, 4] : List Nat))[2]? = ([8, 6, 4] : List Nat)[2]?) ∧ (2 ≤ 8 → (listUpdate ([8, 6, 4] : List Nat) 8 ([8, 6, 4] : List Nat)).drop 2 = listUpdate ([8, 6, 4] : List Nat) (8-2) (([8, 6, 4] : List Nat).drop 2)) ∧ listUpdate ([8, 6, 4] : List Nat) 8 ([8, 6, 4] : List Nat) = ([8, 6, 4] : List Nat).take 8 ++ listUpdate ([8, 6, 4] : List Nat) 0 (([8, 6, 4] : List Nat).drop 8) := by decide

-- lu_cons_0_0
example : listUpdate ((9 : Nat)::([] : List Nat)) 0 ((7 : Nat)::([] : List Nat)) = 9::listUpdate ([] : List Nat) 0 ([] : List Nat) := by decide

-- lu_append_0_0
example : listUpdate ([] : List Nat) 0 (([] : List Nat) ++ ([] : List Nat)) = ([] : List Nat) ++ ([] : List Nat) := by decide

-- lu_cons_0_1
example : listUpdate ((9 : Nat)::([] : List Nat)) 0 ((7 : Nat)::([1] : List Nat)) = 9::listUpdate ([] : List Nat) 0 ([1] : List Nat) := by decide

-- lu_append_0_1
example : listUpdate ([] : List Nat) 0 (([] : List Nat) ++ ([1] : List Nat)) = ([] : List Nat) ++ ([1] : List Nat) := by decide

-- lu_cons_0_2
example : listUpdate ((9 : Nat)::([] : List Nat)) 0 ((7 : Nat)::([2, 4] : List Nat)) = 9::listUpdate ([] : List Nat) 0 ([2, 4] : List Nat) := by decide

-- lu_append_0_2
example : listUpdate ([] : List Nat) 0 (([] : List Nat) ++ ([2, 4] : List Nat)) = ([] : List Nat) ++ ([2, 4] : List Nat) := by decide

-- lu_cons_0_3
example : listUpdate ((9 : Nat)::([] : List Nat)) 0 ((7 : Nat)::([8, 6, 4] : List Nat)) = 9::listUpdate ([] : List Nat) 0 ([8, 6, 4] : List Nat) := by decide

-- lu_append_0_3
example : listUpdate ([] : List Nat) 0 (([] : List Nat) ++ ([8, 6, 4] : List Nat)) = ([] : List Nat) ++ ([8, 6, 4] : List Nat) := by decide

-- lu_nil_0_0
example : listUpdate ([] : List Nat) 0 [] = [] := by decide

-- lu_single_0_0
example : ([] : List Nat).set 0 9 = ([] : List Nat).take 0 ++ (([] : List Nat).drop 0).set 0 9 := by decide

-- lu_nil_0_1
example : listUpdate ([] : List Nat) 1 [] = [] := by decide

-- lu_single_0_1
example : ([] : List Nat).set 1 9 = ([] : List Nat).take 1 ++ (([] : List Nat).drop 1).set 0 9 := by decide

-- lu_nil_0_3
example : listUpdate ([] : List Nat) 3 [] = [] := by decide

-- lu_single_0_3
example : ([] : List Nat).set 3 9 = ([] : List Nat).take 3 ++ (([] : List Nat).drop 3).set 0 9 := by decide

-- lu_nil_0_8
example : listUpdate ([] : List Nat) 8 [] = [] := by decide

-- lu_single_0_8
example : ([] : List Nat).set 8 9 = ([] : List Nat).take 8 ++ (([] : List Nat).drop 8).set 0 9 := by decide

-- lu_cons_1_0
example : listUpdate ((9 : Nat)::([1] : List Nat)) 0 ((7 : Nat)::([] : List Nat)) = 9::listUpdate ([1] : List Nat) 0 ([] : List Nat) := by decide

-- lu_append_1_0
example : listUpdate ([1] : List Nat) 0 (([1] : List Nat) ++ ([] : List Nat)) = ([1] : List Nat) ++ ([] : List Nat) := by decide

-- lu_cons_1_1
example : listUpdate ((9 : Nat)::([1] : List Nat)) 0 ((7 : Nat)::([1] : List Nat)) = 9::listUpdate ([1] : List Nat) 0 ([1] : List Nat) := by decide

-- lu_append_1_1
example : listUpdate ([1] : List Nat) 0 (([1] : List Nat) ++ ([1] : List Nat)) = ([1] : List Nat) ++ ([1] : List Nat) := by decide

-- lu_cons_1_2
example : listUpdate ((9 : Nat)::([1] : List Nat)) 0 ((7 : Nat)::([2, 4] : List Nat)) = 9::listUpdate ([1] : List Nat) 0 ([2, 4] : List Nat) := by decide

-- lu_append_1_2
example : listUpdate ([1] : List Nat) 0 (([1] : List Nat) ++ ([2, 4] : List Nat)) = ([1] : List Nat) ++ ([2, 4] : List Nat) := by decide

-- lu_cons_1_3
example : listUpdate ((9 : Nat)::([1] : List Nat)) 0 ((7 : Nat)::([8, 6, 4] : List Nat)) = 9::listUpdate ([1] : List Nat) 0 ([8, 6, 4] : List Nat) := by decide

-- lu_append_1_3
example : listUpdate ([1] : List Nat) 0 (([1] : List Nat) ++ ([8, 6, 4] : List Nat)) = ([1] : List Nat) ++ ([8, 6, 4] : List Nat) := by decide

-- lu_nil_1_0
example : listUpdate ([1] : List Nat) 0 [] = [] := by decide

-- lu_single_1_0
example : ([1] : List Nat).set 0 9 = ([1] : List Nat).take 0 ++ (([1] : List Nat).drop 0).set 0 9 := by decide

-- lu_nil_1_1
example : listUpdate ([1] : List Nat) 1 [] = [] := by decide

-- lu_single_1_1
example : ([1] : List Nat).set 1 9 = ([1] : List Nat).take 1 ++ (([1] : List Nat).drop 1).set 0 9 := by decide

-- lu_nil_1_3
example : listUpdate ([1] : List Nat) 3 [] = [] := by decide

-- lu_single_1_3
example : ([1] : List Nat).set 3 9 = ([1] : List Nat).take 3 ++ (([1] : List Nat).drop 3).set 0 9 := by decide

-- lu_nil_1_8
example : listUpdate ([1] : List Nat) 8 [] = [] := by decide

-- lu_single_1_8
example : ([1] : List Nat).set 8 9 = ([1] : List Nat).take 8 ++ (([1] : List Nat).drop 8).set 0 9 := by decide

-- lu_cons_2_0
example : listUpdate ((9 : Nat)::([2, 4] : List Nat)) 0 ((7 : Nat)::([] : List Nat)) = 9::listUpdate ([2, 4] : List Nat) 0 ([] : List Nat) := by decide

-- lu_append_2_0
example : listUpdate ([2, 4] : List Nat) 0 (([4, 2] : List Nat) ++ ([] : List Nat)) = ([2, 4] : List Nat) ++ ([] : List Nat) := by decide

-- lu_cons_2_1
example : listUpdate ((9 : Nat)::([2, 4] : List Nat)) 0 ((7 : Nat)::([1] : List Nat)) = 9::listUpdate ([2, 4] : List Nat) 0 ([1] : List Nat) := by decide

-- lu_append_2_1
example : listUpdate ([2, 4] : List Nat) 0 (([4, 2] : List Nat) ++ ([1] : List Nat)) = ([2, 4] : List Nat) ++ ([1] : List Nat) := by decide

-- lu_cons_2_2
example : listUpdate ((9 : Nat)::([2, 4] : List Nat)) 0 ((7 : Nat)::([2, 4] : List Nat)) = 9::listUpdate ([2, 4] : List Nat) 0 ([2, 4] : List Nat) := by decide

-- lu_append_2_2
example : listUpdate ([2, 4] : List Nat) 0 (([4, 2] : List Nat) ++ ([2, 4] : List Nat)) = ([2, 4] : List Nat) ++ ([2, 4] : List Nat) := by decide

-- lu_cons_2_3
example : listUpdate ((9 : Nat)::([2, 4] : List Nat)) 0 ((7 : Nat)::([8, 6, 4] : List Nat)) = 9::listUpdate ([2, 4] : List Nat) 0 ([8, 6, 4] : List Nat) := by decide

-- lu_append_2_3
example : listUpdate ([2, 4] : List Nat) 0 (([4, 2] : List Nat) ++ ([8, 6, 4] : List Nat)) = ([2, 4] : List Nat) ++ ([8, 6, 4] : List Nat) := by decide

-- lu_nil_2_0
example : listUpdate ([2, 4] : List Nat) 0 [] = [] := by decide

-- lu_single_2_0
example : ([2, 4] : List Nat).set 0 9 = ([2, 4] : List Nat).take 0 ++ (([2, 4] : List Nat).drop 0).set 0 9 := by decide

-- lu_nil_2_1
example : listUpdate ([2, 4] : List Nat) 1 [] = [] := by decide

-- lu_single_2_1
example : ([2, 4] : List Nat).set 1 9 = ([2, 4] : List Nat).take 1 ++ (([2, 4] : List Nat).drop 1).set 0 9 := by decide

-- lu_nil_2_3
example : listUpdate ([2, 4] : List Nat) 3 [] = [] := by decide

-- lu_single_2_3
example : ([2, 4] : List Nat).set 3 9 = ([2, 4] : List Nat).take 3 ++ (([2, 4] : List Nat).drop 3).set 0 9 := by decide

-- lu_nil_2_8
example : listUpdate ([2, 4] : List Nat) 8 [] = [] := by decide

-- lu_single_2_8
example : ([2, 4] : List Nat).set 8 9 = ([2, 4] : List Nat).take 8 ++ (([2, 4] : List Nat).drop 8).set 0 9 := by decide

-- lu_cons_3_0
example : listUpdate ((9 : Nat)::([8, 6, 4] : List Nat)) 0 ((7 : Nat)::([] : List Nat)) = 9::listUpdate ([8, 6, 4] : List Nat) 0 ([] : List Nat) := by decide

-- lu_append_3_0
example : listUpdate ([8, 6, 4] : List Nat) 0 (([4, 6, 8] : List Nat) ++ ([] : List Nat)) = ([8, 6, 4] : List Nat) ++ ([] : List Nat) := by decide

-- lu_cons_3_1
example : listUpdate ((9 : Nat)::([8, 6, 4] : List Nat)) 0 ((7 : Nat)::([1] : List Nat)) = 9::listUpdate ([8, 6, 4] : List Nat) 0 ([1] : List Nat) := by decide

-- lu_append_3_1
example : listUpdate ([8, 6, 4] : List Nat) 0 (([4, 6, 8] : List Nat) ++ ([1] : List Nat)) = ([8, 6, 4] : List Nat) ++ ([1] : List Nat) := by decide

-- lu_cons_3_2
example : listUpdate ((9 : Nat)::([8, 6, 4] : List Nat)) 0 ((7 : Nat)::([2, 4] : List Nat)) = 9::listUpdate ([8, 6, 4] : List Nat) 0 ([2, 4] : List Nat) := by decide

-- lu_append_3_2
example : listUpdate ([8, 6, 4] : List Nat) 0 (([4, 6, 8] : List Nat) ++ ([2, 4] : List Nat)) = ([8, 6, 4] : List Nat) ++ ([2, 4] : List Nat) := by decide

-- lu_cons_3_3
example : listUpdate ((9 : Nat)::([8, 6, 4] : List Nat)) 0 ((7 : Nat)::([8, 6, 4] : List Nat)) = 9::listUpdate ([8, 6, 4] : List Nat) 0 ([8, 6, 4] : List Nat) := by decide

-- lu_append_3_3
example : listUpdate ([8, 6, 4] : List Nat) 0 (([4, 6, 8] : List Nat) ++ ([8, 6, 4] : List Nat)) = ([8, 6, 4] : List Nat) ++ ([8, 6, 4] : List Nat) := by decide

-- lu_nil_3_0
example : listUpdate ([8, 6, 4] : List Nat) 0 [] = [] := by decide

-- lu_single_3_0
example : ([8, 6, 4] : List Nat).set 0 9 = ([8, 6, 4] : List Nat).take 0 ++ (([8, 6, 4] : List Nat).drop 0).set 0 9 := by decide

-- lu_nil_3_1
example : listUpdate ([8, 6, 4] : List Nat) 1 [] = [] := by decide

-- lu_single_3_1
example : ([8, 6, 4] : List Nat).set 1 9 = ([8, 6, 4] : List Nat).take 1 ++ (([8, 6, 4] : List Nat).drop 1).set 0 9 := by decide

-- lu_nil_3_3
example : listUpdate ([8, 6, 4] : List Nat) 3 [] = [] := by decide

-- lu_single_3_3
example : ([8, 6, 4] : List Nat).set 3 9 = ([8, 6, 4] : List Nat).take 3 ++ (([8, 6, 4] : List Nat).drop 3).set 0 9 := by decide

-- lu_nil_3_8
example : listUpdate ([8, 6, 4] : List Nat) 8 [] = [] := by decide

-- lu_single_3_8
example : ([8, 6, 4] : List Nat).set 8 9 = ([8, 6, 4] : List Nat).take 8 ++ (([8, 6, 4] : List Nat).drop 8).set 0 9 := by decide


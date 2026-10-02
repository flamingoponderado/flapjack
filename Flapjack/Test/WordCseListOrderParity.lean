import Flapjack.Compiler.Backend.WordCse.Proofs.ListOrder
open Flapjack.Compiler.Backend.WordCse

-- lo_value_0_0
example : listCmp [] [] = .eq := by decide

-- lo_eq_0_0
example (xs ys : List Nat) : listCmp ([] ++ xs) ([] ++ ys) = .eq ↔ ([] ++ xs) = ([] ++ ys) := listCmpEqCorrect ([] ++ xs) ([] ++ ys)

-- lo_reverse_0_0
example (xs ys : List Nat) : listCmp ([] ++ xs) ([] ++ ys) = .gt ↔ listCmp ([] ++ ys) ([] ++ xs) = .lt := antisymListCmp ([] ++ xs) ([] ++ ys)

-- lo_value_0_1
example : listCmp [] [0] = .lt := by decide

-- lo_eq_0_1
example (xs ys : List Nat) : listCmp ([] ++ xs) ([0] ++ ys) = .eq ↔ ([] ++ xs) = ([0] ++ ys) := listCmpEqCorrect ([] ++ xs) ([0] ++ ys)

-- lo_reverse_0_1
example (xs ys : List Nat) : listCmp ([] ++ xs) ([0] ++ ys) = .gt ↔ listCmp ([0] ++ ys) ([] ++ xs) = .lt := antisymListCmp ([] ++ xs) ([0] ++ ys)

-- lo_value_0_2
example : listCmp [] [1] = .lt := by decide

-- lo_eq_0_2
example (xs ys : List Nat) : listCmp ([] ++ xs) ([1] ++ ys) = .eq ↔ ([] ++ xs) = ([1] ++ ys) := listCmpEqCorrect ([] ++ xs) ([1] ++ ys)

-- lo_reverse_0_2
example (xs ys : List Nat) : listCmp ([] ++ xs) ([1] ++ ys) = .gt ↔ listCmp ([1] ++ ys) ([] ++ xs) = .lt := antisymListCmp ([] ++ xs) ([1] ++ ys)

-- lo_value_0_3
example : listCmp [] [0,0] = .lt := by decide

-- lo_eq_0_3
example (xs ys : List Nat) : listCmp ([] ++ xs) ([0,0] ++ ys) = .eq ↔ ([] ++ xs) = ([0,0] ++ ys) := listCmpEqCorrect ([] ++ xs) ([0,0] ++ ys)

-- lo_reverse_0_3
example (xs ys : List Nat) : listCmp ([] ++ xs) ([0,0] ++ ys) = .gt ↔ listCmp ([0,0] ++ ys) ([] ++ xs) = .lt := antisymListCmp ([] ++ xs) ([0,0] ++ ys)

-- lo_value_0_4
example : listCmp [] [0,1] = .lt := by decide

-- lo_eq_0_4
example (xs ys : List Nat) : listCmp ([] ++ xs) ([0,1] ++ ys) = .eq ↔ ([] ++ xs) = ([0,1] ++ ys) := listCmpEqCorrect ([] ++ xs) ([0,1] ++ ys)

-- lo_reverse_0_4
example (xs ys : List Nat) : listCmp ([] ++ xs) ([0,1] ++ ys) = .gt ↔ listCmp ([0,1] ++ ys) ([] ++ xs) = .lt := antisymListCmp ([] ++ xs) ([0,1] ++ ys)

-- lo_value_0_5
example : listCmp [] [1,0] = .lt := by decide

-- lo_eq_0_5
example (xs ys : List Nat) : listCmp ([] ++ xs) ([1,0] ++ ys) = .eq ↔ ([] ++ xs) = ([1,0] ++ ys) := listCmpEqCorrect ([] ++ xs) ([1,0] ++ ys)

-- lo_reverse_0_5
example (xs ys : List Nat) : listCmp ([] ++ xs) ([1,0] ++ ys) = .gt ↔ listCmp ([1,0] ++ ys) ([] ++ xs) = .lt := antisymListCmp ([] ++ xs) ([1,0] ++ ys)

-- lo_value_0_6
example : listCmp [] [1208925819614629174706183] = .lt := by decide

-- lo_eq_0_6
example (xs ys : List Nat) : listCmp ([] ++ xs) ([1208925819614629174706183] ++ ys) = .eq ↔ ([] ++ xs) = ([1208925819614629174706183] ++ ys) := listCmpEqCorrect ([] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_reverse_0_6
example (xs ys : List Nat) : listCmp ([] ++ xs) ([1208925819614629174706183] ++ ys) = .gt ↔ listCmp ([1208925819614629174706183] ++ ys) ([] ++ xs) = .lt := antisymListCmp ([] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_value_0_7
example : listCmp [] [0,0,0,0,0,0,0,0,0,0,0,0,1] = .lt := by decide

-- lo_eq_0_7
example (xs ys : List Nat) : listCmp ([] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .eq ↔ ([] ++ xs) = ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) := listCmpEqCorrect ([] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_reverse_0_7
example (xs ys : List Nat) : listCmp ([] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .gt ↔ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([] ++ xs) = .lt := antisymListCmp ([] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_value_1_0
example : listCmp [0] [] = .gt := by decide

-- lo_eq_1_0
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([] ++ ys) = .eq ↔ ([0] ++ xs) = ([] ++ ys) := listCmpEqCorrect ([0] ++ xs) ([] ++ ys)

-- lo_reverse_1_0
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([] ++ ys) = .gt ↔ listCmp ([] ++ ys) ([0] ++ xs) = .lt := antisymListCmp ([0] ++ xs) ([] ++ ys)

-- lo_value_1_1
example : listCmp [0] [0] = .eq := by decide

-- lo_eq_1_1
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([0] ++ ys) = .eq ↔ ([0] ++ xs) = ([0] ++ ys) := listCmpEqCorrect ([0] ++ xs) ([0] ++ ys)

-- lo_reverse_1_1
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([0] ++ ys) = .gt ↔ listCmp ([0] ++ ys) ([0] ++ xs) = .lt := antisymListCmp ([0] ++ xs) ([0] ++ ys)

-- lo_value_1_2
example : listCmp [0] [1] = .lt := by decide

-- lo_eq_1_2
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([1] ++ ys) = .eq ↔ ([0] ++ xs) = ([1] ++ ys) := listCmpEqCorrect ([0] ++ xs) ([1] ++ ys)

-- lo_reverse_1_2
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([1] ++ ys) = .gt ↔ listCmp ([1] ++ ys) ([0] ++ xs) = .lt := antisymListCmp ([0] ++ xs) ([1] ++ ys)

-- lo_value_1_3
example : listCmp [0] [0,0] = .lt := by decide

-- lo_eq_1_3
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([0,0] ++ ys) = .eq ↔ ([0] ++ xs) = ([0,0] ++ ys) := listCmpEqCorrect ([0] ++ xs) ([0,0] ++ ys)

-- lo_reverse_1_3
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([0,0] ++ ys) = .gt ↔ listCmp ([0,0] ++ ys) ([0] ++ xs) = .lt := antisymListCmp ([0] ++ xs) ([0,0] ++ ys)

-- lo_value_1_4
example : listCmp [0] [0,1] = .lt := by decide

-- lo_eq_1_4
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([0,1] ++ ys) = .eq ↔ ([0] ++ xs) = ([0,1] ++ ys) := listCmpEqCorrect ([0] ++ xs) ([0,1] ++ ys)

-- lo_reverse_1_4
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([0,1] ++ ys) = .gt ↔ listCmp ([0,1] ++ ys) ([0] ++ xs) = .lt := antisymListCmp ([0] ++ xs) ([0,1] ++ ys)

-- lo_value_1_5
example : listCmp [0] [1,0] = .lt := by decide

-- lo_eq_1_5
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([1,0] ++ ys) = .eq ↔ ([0] ++ xs) = ([1,0] ++ ys) := listCmpEqCorrect ([0] ++ xs) ([1,0] ++ ys)

-- lo_reverse_1_5
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([1,0] ++ ys) = .gt ↔ listCmp ([1,0] ++ ys) ([0] ++ xs) = .lt := antisymListCmp ([0] ++ xs) ([1,0] ++ ys)

-- lo_value_1_6
example : listCmp [0] [1208925819614629174706183] = .lt := by decide

-- lo_eq_1_6
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([1208925819614629174706183] ++ ys) = .eq ↔ ([0] ++ xs) = ([1208925819614629174706183] ++ ys) := listCmpEqCorrect ([0] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_reverse_1_6
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([1208925819614629174706183] ++ ys) = .gt ↔ listCmp ([1208925819614629174706183] ++ ys) ([0] ++ xs) = .lt := antisymListCmp ([0] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_value_1_7
example : listCmp [0] [0,0,0,0,0,0,0,0,0,0,0,0,1] = .lt := by decide

-- lo_eq_1_7
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .eq ↔ ([0] ++ xs) = ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) := listCmpEqCorrect ([0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_reverse_1_7
example (xs ys : List Nat) : listCmp ([0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .gt ↔ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([0] ++ xs) = .lt := antisymListCmp ([0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_value_2_0
example : listCmp [1] [] = .gt := by decide

-- lo_eq_2_0
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([] ++ ys) = .eq ↔ ([1] ++ xs) = ([] ++ ys) := listCmpEqCorrect ([1] ++ xs) ([] ++ ys)

-- lo_reverse_2_0
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([] ++ ys) = .gt ↔ listCmp ([] ++ ys) ([1] ++ xs) = .lt := antisymListCmp ([1] ++ xs) ([] ++ ys)

-- lo_value_2_1
example : listCmp [1] [0] = .gt := by decide

-- lo_eq_2_1
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([0] ++ ys) = .eq ↔ ([1] ++ xs) = ([0] ++ ys) := listCmpEqCorrect ([1] ++ xs) ([0] ++ ys)

-- lo_reverse_2_1
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([0] ++ ys) = .gt ↔ listCmp ([0] ++ ys) ([1] ++ xs) = .lt := antisymListCmp ([1] ++ xs) ([0] ++ ys)

-- lo_value_2_2
example : listCmp [1] [1] = .eq := by decide

-- lo_eq_2_2
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([1] ++ ys) = .eq ↔ ([1] ++ xs) = ([1] ++ ys) := listCmpEqCorrect ([1] ++ xs) ([1] ++ ys)

-- lo_reverse_2_2
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([1] ++ ys) = .gt ↔ listCmp ([1] ++ ys) ([1] ++ xs) = .lt := antisymListCmp ([1] ++ xs) ([1] ++ ys)

-- lo_value_2_3
example : listCmp [1] [0,0] = .gt := by decide

-- lo_eq_2_3
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([0,0] ++ ys) = .eq ↔ ([1] ++ xs) = ([0,0] ++ ys) := listCmpEqCorrect ([1] ++ xs) ([0,0] ++ ys)

-- lo_reverse_2_3
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([0,0] ++ ys) = .gt ↔ listCmp ([0,0] ++ ys) ([1] ++ xs) = .lt := antisymListCmp ([1] ++ xs) ([0,0] ++ ys)

-- lo_value_2_4
example : listCmp [1] [0,1] = .gt := by decide

-- lo_eq_2_4
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([0,1] ++ ys) = .eq ↔ ([1] ++ xs) = ([0,1] ++ ys) := listCmpEqCorrect ([1] ++ xs) ([0,1] ++ ys)

-- lo_reverse_2_4
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([0,1] ++ ys) = .gt ↔ listCmp ([0,1] ++ ys) ([1] ++ xs) = .lt := antisymListCmp ([1] ++ xs) ([0,1] ++ ys)

-- lo_value_2_5
example : listCmp [1] [1,0] = .lt := by decide

-- lo_eq_2_5
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([1,0] ++ ys) = .eq ↔ ([1] ++ xs) = ([1,0] ++ ys) := listCmpEqCorrect ([1] ++ xs) ([1,0] ++ ys)

-- lo_reverse_2_5
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([1,0] ++ ys) = .gt ↔ listCmp ([1,0] ++ ys) ([1] ++ xs) = .lt := antisymListCmp ([1] ++ xs) ([1,0] ++ ys)

-- lo_value_2_6
example : listCmp [1] [1208925819614629174706183] = .lt := by decide

-- lo_eq_2_6
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([1208925819614629174706183] ++ ys) = .eq ↔ ([1] ++ xs) = ([1208925819614629174706183] ++ ys) := listCmpEqCorrect ([1] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_reverse_2_6
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([1208925819614629174706183] ++ ys) = .gt ↔ listCmp ([1208925819614629174706183] ++ ys) ([1] ++ xs) = .lt := antisymListCmp ([1] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_value_2_7
example : listCmp [1] [0,0,0,0,0,0,0,0,0,0,0,0,1] = .gt := by decide

-- lo_eq_2_7
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .eq ↔ ([1] ++ xs) = ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) := listCmpEqCorrect ([1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_reverse_2_7
example (xs ys : List Nat) : listCmp ([1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .gt ↔ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([1] ++ xs) = .lt := antisymListCmp ([1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_value_3_0
example : listCmp [0,0] [] = .gt := by decide

-- lo_eq_3_0
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([] ++ ys) = .eq ↔ ([0,0] ++ xs) = ([] ++ ys) := listCmpEqCorrect ([0,0] ++ xs) ([] ++ ys)

-- lo_reverse_3_0
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([] ++ ys) = .gt ↔ listCmp ([] ++ ys) ([0,0] ++ xs) = .lt := antisymListCmp ([0,0] ++ xs) ([] ++ ys)

-- lo_value_3_1
example : listCmp [0,0] [0] = .gt := by decide

-- lo_eq_3_1
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([0] ++ ys) = .eq ↔ ([0,0] ++ xs) = ([0] ++ ys) := listCmpEqCorrect ([0,0] ++ xs) ([0] ++ ys)

-- lo_reverse_3_1
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([0] ++ ys) = .gt ↔ listCmp ([0] ++ ys) ([0,0] ++ xs) = .lt := antisymListCmp ([0,0] ++ xs) ([0] ++ ys)

-- lo_value_3_2
example : listCmp [0,0] [1] = .lt := by decide

-- lo_eq_3_2
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([1] ++ ys) = .eq ↔ ([0,0] ++ xs) = ([1] ++ ys) := listCmpEqCorrect ([0,0] ++ xs) ([1] ++ ys)

-- lo_reverse_3_2
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([1] ++ ys) = .gt ↔ listCmp ([1] ++ ys) ([0,0] ++ xs) = .lt := antisymListCmp ([0,0] ++ xs) ([1] ++ ys)

-- lo_value_3_3
example : listCmp [0,0] [0,0] = .eq := by decide

-- lo_eq_3_3
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([0,0] ++ ys) = .eq ↔ ([0,0] ++ xs) = ([0,0] ++ ys) := listCmpEqCorrect ([0,0] ++ xs) ([0,0] ++ ys)

-- lo_reverse_3_3
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([0,0] ++ ys) = .gt ↔ listCmp ([0,0] ++ ys) ([0,0] ++ xs) = .lt := antisymListCmp ([0,0] ++ xs) ([0,0] ++ ys)

-- lo_value_3_4
example : listCmp [0,0] [0,1] = .lt := by decide

-- lo_eq_3_4
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([0,1] ++ ys) = .eq ↔ ([0,0] ++ xs) = ([0,1] ++ ys) := listCmpEqCorrect ([0,0] ++ xs) ([0,1] ++ ys)

-- lo_reverse_3_4
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([0,1] ++ ys) = .gt ↔ listCmp ([0,1] ++ ys) ([0,0] ++ xs) = .lt := antisymListCmp ([0,0] ++ xs) ([0,1] ++ ys)

-- lo_value_3_5
example : listCmp [0,0] [1,0] = .lt := by decide

-- lo_eq_3_5
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([1,0] ++ ys) = .eq ↔ ([0,0] ++ xs) = ([1,0] ++ ys) := listCmpEqCorrect ([0,0] ++ xs) ([1,0] ++ ys)

-- lo_reverse_3_5
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([1,0] ++ ys) = .gt ↔ listCmp ([1,0] ++ ys) ([0,0] ++ xs) = .lt := antisymListCmp ([0,0] ++ xs) ([1,0] ++ ys)

-- lo_value_3_6
example : listCmp [0,0] [1208925819614629174706183] = .lt := by decide

-- lo_eq_3_6
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([1208925819614629174706183] ++ ys) = .eq ↔ ([0,0] ++ xs) = ([1208925819614629174706183] ++ ys) := listCmpEqCorrect ([0,0] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_reverse_3_6
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([1208925819614629174706183] ++ ys) = .gt ↔ listCmp ([1208925819614629174706183] ++ ys) ([0,0] ++ xs) = .lt := antisymListCmp ([0,0] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_value_3_7
example : listCmp [0,0] [0,0,0,0,0,0,0,0,0,0,0,0,1] = .lt := by decide

-- lo_eq_3_7
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .eq ↔ ([0,0] ++ xs) = ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) := listCmpEqCorrect ([0,0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_reverse_3_7
example (xs ys : List Nat) : listCmp ([0,0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .gt ↔ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([0,0] ++ xs) = .lt := antisymListCmp ([0,0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_value_4_0
example : listCmp [0,1] [] = .gt := by decide

-- lo_eq_4_0
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([] ++ ys) = .eq ↔ ([0,1] ++ xs) = ([] ++ ys) := listCmpEqCorrect ([0,1] ++ xs) ([] ++ ys)

-- lo_reverse_4_0
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([] ++ ys) = .gt ↔ listCmp ([] ++ ys) ([0,1] ++ xs) = .lt := antisymListCmp ([0,1] ++ xs) ([] ++ ys)

-- lo_value_4_1
example : listCmp [0,1] [0] = .gt := by decide

-- lo_eq_4_1
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([0] ++ ys) = .eq ↔ ([0,1] ++ xs) = ([0] ++ ys) := listCmpEqCorrect ([0,1] ++ xs) ([0] ++ ys)

-- lo_reverse_4_1
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([0] ++ ys) = .gt ↔ listCmp ([0] ++ ys) ([0,1] ++ xs) = .lt := antisymListCmp ([0,1] ++ xs) ([0] ++ ys)

-- lo_value_4_2
example : listCmp [0,1] [1] = .lt := by decide

-- lo_eq_4_2
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([1] ++ ys) = .eq ↔ ([0,1] ++ xs) = ([1] ++ ys) := listCmpEqCorrect ([0,1] ++ xs) ([1] ++ ys)

-- lo_reverse_4_2
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([1] ++ ys) = .gt ↔ listCmp ([1] ++ ys) ([0,1] ++ xs) = .lt := antisymListCmp ([0,1] ++ xs) ([1] ++ ys)

-- lo_value_4_3
example : listCmp [0,1] [0,0] = .gt := by decide

-- lo_eq_4_3
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([0,0] ++ ys) = .eq ↔ ([0,1] ++ xs) = ([0,0] ++ ys) := listCmpEqCorrect ([0,1] ++ xs) ([0,0] ++ ys)

-- lo_reverse_4_3
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([0,0] ++ ys) = .gt ↔ listCmp ([0,0] ++ ys) ([0,1] ++ xs) = .lt := antisymListCmp ([0,1] ++ xs) ([0,0] ++ ys)

-- lo_value_4_4
example : listCmp [0,1] [0,1] = .eq := by decide

-- lo_eq_4_4
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([0,1] ++ ys) = .eq ↔ ([0,1] ++ xs) = ([0,1] ++ ys) := listCmpEqCorrect ([0,1] ++ xs) ([0,1] ++ ys)

-- lo_reverse_4_4
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([0,1] ++ ys) = .gt ↔ listCmp ([0,1] ++ ys) ([0,1] ++ xs) = .lt := antisymListCmp ([0,1] ++ xs) ([0,1] ++ ys)

-- lo_value_4_5
example : listCmp [0,1] [1,0] = .lt := by decide

-- lo_eq_4_5
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([1,0] ++ ys) = .eq ↔ ([0,1] ++ xs) = ([1,0] ++ ys) := listCmpEqCorrect ([0,1] ++ xs) ([1,0] ++ ys)

-- lo_reverse_4_5
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([1,0] ++ ys) = .gt ↔ listCmp ([1,0] ++ ys) ([0,1] ++ xs) = .lt := antisymListCmp ([0,1] ++ xs) ([1,0] ++ ys)

-- lo_value_4_6
example : listCmp [0,1] [1208925819614629174706183] = .lt := by decide

-- lo_eq_4_6
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([1208925819614629174706183] ++ ys) = .eq ↔ ([0,1] ++ xs) = ([1208925819614629174706183] ++ ys) := listCmpEqCorrect ([0,1] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_reverse_4_6
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([1208925819614629174706183] ++ ys) = .gt ↔ listCmp ([1208925819614629174706183] ++ ys) ([0,1] ++ xs) = .lt := antisymListCmp ([0,1] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_value_4_7
example : listCmp [0,1] [0,0,0,0,0,0,0,0,0,0,0,0,1] = .gt := by decide

-- lo_eq_4_7
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .eq ↔ ([0,1] ++ xs) = ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) := listCmpEqCorrect ([0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_reverse_4_7
example (xs ys : List Nat) : listCmp ([0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .gt ↔ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([0,1] ++ xs) = .lt := antisymListCmp ([0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_value_5_0
example : listCmp [1,0] [] = .gt := by decide

-- lo_eq_5_0
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([] ++ ys) = .eq ↔ ([1,0] ++ xs) = ([] ++ ys) := listCmpEqCorrect ([1,0] ++ xs) ([] ++ ys)

-- lo_reverse_5_0
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([] ++ ys) = .gt ↔ listCmp ([] ++ ys) ([1,0] ++ xs) = .lt := antisymListCmp ([1,0] ++ xs) ([] ++ ys)

-- lo_value_5_1
example : listCmp [1,0] [0] = .gt := by decide

-- lo_eq_5_1
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([0] ++ ys) = .eq ↔ ([1,0] ++ xs) = ([0] ++ ys) := listCmpEqCorrect ([1,0] ++ xs) ([0] ++ ys)

-- lo_reverse_5_1
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([0] ++ ys) = .gt ↔ listCmp ([0] ++ ys) ([1,0] ++ xs) = .lt := antisymListCmp ([1,0] ++ xs) ([0] ++ ys)

-- lo_value_5_2
example : listCmp [1,0] [1] = .gt := by decide

-- lo_eq_5_2
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([1] ++ ys) = .eq ↔ ([1,0] ++ xs) = ([1] ++ ys) := listCmpEqCorrect ([1,0] ++ xs) ([1] ++ ys)

-- lo_reverse_5_2
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([1] ++ ys) = .gt ↔ listCmp ([1] ++ ys) ([1,0] ++ xs) = .lt := antisymListCmp ([1,0] ++ xs) ([1] ++ ys)

-- lo_value_5_3
example : listCmp [1,0] [0,0] = .gt := by decide

-- lo_eq_5_3
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([0,0] ++ ys) = .eq ↔ ([1,0] ++ xs) = ([0,0] ++ ys) := listCmpEqCorrect ([1,0] ++ xs) ([0,0] ++ ys)

-- lo_reverse_5_3
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([0,0] ++ ys) = .gt ↔ listCmp ([0,0] ++ ys) ([1,0] ++ xs) = .lt := antisymListCmp ([1,0] ++ xs) ([0,0] ++ ys)

-- lo_value_5_4
example : listCmp [1,0] [0,1] = .gt := by decide

-- lo_eq_5_4
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([0,1] ++ ys) = .eq ↔ ([1,0] ++ xs) = ([0,1] ++ ys) := listCmpEqCorrect ([1,0] ++ xs) ([0,1] ++ ys)

-- lo_reverse_5_4
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([0,1] ++ ys) = .gt ↔ listCmp ([0,1] ++ ys) ([1,0] ++ xs) = .lt := antisymListCmp ([1,0] ++ xs) ([0,1] ++ ys)

-- lo_value_5_5
example : listCmp [1,0] [1,0] = .eq := by decide

-- lo_eq_5_5
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([1,0] ++ ys) = .eq ↔ ([1,0] ++ xs) = ([1,0] ++ ys) := listCmpEqCorrect ([1,0] ++ xs) ([1,0] ++ ys)

-- lo_reverse_5_5
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([1,0] ++ ys) = .gt ↔ listCmp ([1,0] ++ ys) ([1,0] ++ xs) = .lt := antisymListCmp ([1,0] ++ xs) ([1,0] ++ ys)

-- lo_value_5_6
example : listCmp [1,0] [1208925819614629174706183] = .lt := by decide

-- lo_eq_5_6
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([1208925819614629174706183] ++ ys) = .eq ↔ ([1,0] ++ xs) = ([1208925819614629174706183] ++ ys) := listCmpEqCorrect ([1,0] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_reverse_5_6
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([1208925819614629174706183] ++ ys) = .gt ↔ listCmp ([1208925819614629174706183] ++ ys) ([1,0] ++ xs) = .lt := antisymListCmp ([1,0] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_value_5_7
example : listCmp [1,0] [0,0,0,0,0,0,0,0,0,0,0,0,1] = .gt := by decide

-- lo_eq_5_7
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .eq ↔ ([1,0] ++ xs) = ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) := listCmpEqCorrect ([1,0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_reverse_5_7
example (xs ys : List Nat) : listCmp ([1,0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .gt ↔ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([1,0] ++ xs) = .lt := antisymListCmp ([1,0] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_value_6_0
example : listCmp [1208925819614629174706183] [] = .gt := by decide

-- lo_eq_6_0
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([] ++ ys) = .eq ↔ ([1208925819614629174706183] ++ xs) = ([] ++ ys) := listCmpEqCorrect ([1208925819614629174706183] ++ xs) ([] ++ ys)

-- lo_reverse_6_0
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([] ++ ys) = .gt ↔ listCmp ([] ++ ys) ([1208925819614629174706183] ++ xs) = .lt := antisymListCmp ([1208925819614629174706183] ++ xs) ([] ++ ys)

-- lo_value_6_1
example : listCmp [1208925819614629174706183] [0] = .gt := by decide

-- lo_eq_6_1
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([0] ++ ys) = .eq ↔ ([1208925819614629174706183] ++ xs) = ([0] ++ ys) := listCmpEqCorrect ([1208925819614629174706183] ++ xs) ([0] ++ ys)

-- lo_reverse_6_1
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([0] ++ ys) = .gt ↔ listCmp ([0] ++ ys) ([1208925819614629174706183] ++ xs) = .lt := antisymListCmp ([1208925819614629174706183] ++ xs) ([0] ++ ys)

-- lo_value_6_2
example : listCmp [1208925819614629174706183] [1] = .gt := by decide

-- lo_eq_6_2
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([1] ++ ys) = .eq ↔ ([1208925819614629174706183] ++ xs) = ([1] ++ ys) := listCmpEqCorrect ([1208925819614629174706183] ++ xs) ([1] ++ ys)

-- lo_reverse_6_2
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([1] ++ ys) = .gt ↔ listCmp ([1] ++ ys) ([1208925819614629174706183] ++ xs) = .lt := antisymListCmp ([1208925819614629174706183] ++ xs) ([1] ++ ys)

-- lo_value_6_3
example : listCmp [1208925819614629174706183] [0,0] = .gt := by decide

-- lo_eq_6_3
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([0,0] ++ ys) = .eq ↔ ([1208925819614629174706183] ++ xs) = ([0,0] ++ ys) := listCmpEqCorrect ([1208925819614629174706183] ++ xs) ([0,0] ++ ys)

-- lo_reverse_6_3
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([0,0] ++ ys) = .gt ↔ listCmp ([0,0] ++ ys) ([1208925819614629174706183] ++ xs) = .lt := antisymListCmp ([1208925819614629174706183] ++ xs) ([0,0] ++ ys)

-- lo_value_6_4
example : listCmp [1208925819614629174706183] [0,1] = .gt := by decide

-- lo_eq_6_4
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([0,1] ++ ys) = .eq ↔ ([1208925819614629174706183] ++ xs) = ([0,1] ++ ys) := listCmpEqCorrect ([1208925819614629174706183] ++ xs) ([0,1] ++ ys)

-- lo_reverse_6_4
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([0,1] ++ ys) = .gt ↔ listCmp ([0,1] ++ ys) ([1208925819614629174706183] ++ xs) = .lt := antisymListCmp ([1208925819614629174706183] ++ xs) ([0,1] ++ ys)

-- lo_value_6_5
example : listCmp [1208925819614629174706183] [1,0] = .gt := by decide

-- lo_eq_6_5
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([1,0] ++ ys) = .eq ↔ ([1208925819614629174706183] ++ xs) = ([1,0] ++ ys) := listCmpEqCorrect ([1208925819614629174706183] ++ xs) ([1,0] ++ ys)

-- lo_reverse_6_5
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([1,0] ++ ys) = .gt ↔ listCmp ([1,0] ++ ys) ([1208925819614629174706183] ++ xs) = .lt := antisymListCmp ([1208925819614629174706183] ++ xs) ([1,0] ++ ys)

-- lo_value_6_6
example : listCmp [1208925819614629174706183] [1208925819614629174706183] = .eq := by decide

-- lo_eq_6_6
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([1208925819614629174706183] ++ ys) = .eq ↔ ([1208925819614629174706183] ++ xs) = ([1208925819614629174706183] ++ ys) := listCmpEqCorrect ([1208925819614629174706183] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_reverse_6_6
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([1208925819614629174706183] ++ ys) = .gt ↔ listCmp ([1208925819614629174706183] ++ ys) ([1208925819614629174706183] ++ xs) = .lt := antisymListCmp ([1208925819614629174706183] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_value_6_7
example : listCmp [1208925819614629174706183] [0,0,0,0,0,0,0,0,0,0,0,0,1] = .gt := by decide

-- lo_eq_6_7
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .eq ↔ ([1208925819614629174706183] ++ xs) = ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) := listCmpEqCorrect ([1208925819614629174706183] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_reverse_6_7
example (xs ys : List Nat) : listCmp ([1208925819614629174706183] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .gt ↔ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([1208925819614629174706183] ++ xs) = .lt := antisymListCmp ([1208925819614629174706183] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_value_7_0
example : listCmp [0,0,0,0,0,0,0,0,0,0,0,0,1] [] = .gt := by decide

-- lo_eq_7_0
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([] ++ ys) = .eq ↔ ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = ([] ++ ys) := listCmpEqCorrect ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([] ++ ys)

-- lo_reverse_7_0
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([] ++ ys) = .gt ↔ listCmp ([] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = .lt := antisymListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([] ++ ys)

-- lo_value_7_1
example : listCmp [0,0,0,0,0,0,0,0,0,0,0,0,1] [0] = .gt := by decide

-- lo_eq_7_1
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0] ++ ys) = .eq ↔ ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = ([0] ++ ys) := listCmpEqCorrect ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0] ++ ys)

-- lo_reverse_7_1
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0] ++ ys) = .gt ↔ listCmp ([0] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = .lt := antisymListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0] ++ ys)

-- lo_value_7_2
example : listCmp [0,0,0,0,0,0,0,0,0,0,0,0,1] [1] = .lt := by decide

-- lo_eq_7_2
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1] ++ ys) = .eq ↔ ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = ([1] ++ ys) := listCmpEqCorrect ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1] ++ ys)

-- lo_reverse_7_2
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1] ++ ys) = .gt ↔ listCmp ([1] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = .lt := antisymListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1] ++ ys)

-- lo_value_7_3
example : listCmp [0,0,0,0,0,0,0,0,0,0,0,0,1] [0,0] = .gt := by decide

-- lo_eq_7_3
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,0] ++ ys) = .eq ↔ ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = ([0,0] ++ ys) := listCmpEqCorrect ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,0] ++ ys)

-- lo_reverse_7_3
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,0] ++ ys) = .gt ↔ listCmp ([0,0] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = .lt := antisymListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,0] ++ ys)

-- lo_value_7_4
example : listCmp [0,0,0,0,0,0,0,0,0,0,0,0,1] [0,1] = .lt := by decide

-- lo_eq_7_4
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,1] ++ ys) = .eq ↔ ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = ([0,1] ++ ys) := listCmpEqCorrect ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,1] ++ ys)

-- lo_reverse_7_4
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,1] ++ ys) = .gt ↔ listCmp ([0,1] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = .lt := antisymListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,1] ++ ys)

-- lo_value_7_5
example : listCmp [0,0,0,0,0,0,0,0,0,0,0,0,1] [1,0] = .lt := by decide

-- lo_eq_7_5
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1,0] ++ ys) = .eq ↔ ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = ([1,0] ++ ys) := listCmpEqCorrect ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1,0] ++ ys)

-- lo_reverse_7_5
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1,0] ++ ys) = .gt ↔ listCmp ([1,0] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = .lt := antisymListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1,0] ++ ys)

-- lo_value_7_6
example : listCmp [0,0,0,0,0,0,0,0,0,0,0,0,1] [1208925819614629174706183] = .lt := by decide

-- lo_eq_7_6
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1208925819614629174706183] ++ ys) = .eq ↔ ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = ([1208925819614629174706183] ++ ys) := listCmpEqCorrect ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_reverse_7_6
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1208925819614629174706183] ++ ys) = .gt ↔ listCmp ([1208925819614629174706183] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = .lt := antisymListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1208925819614629174706183] ++ ys)

-- lo_value_7_7
example : listCmp [0,0,0,0,0,0,0,0,0,0,0,0,1] [0,0,0,0,0,0,0,0,0,0,0,0,1] = .eq := by decide

-- lo_eq_7_7
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .eq ↔ ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) := listCmpEqCorrect ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_reverse_7_7
example (xs ys : List Nat) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .gt ↔ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) = .lt := antisymListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys)

-- lo_transit_0
example (xs ys zs : List Nat) (h : listCmp ([] ++ xs) ([0] ++ ys) = .lt ∧ listCmp ([0] ++ ys) ([0,0] ++ zs) = .lt) : listCmp ([] ++ xs) ([0,0] ++ zs) = .lt := transitListCmp ([] ++ xs) ([0] ++ ys) ([0,0] ++ zs) h

-- lo_transit_1
example (xs ys zs : List Nat) (h : listCmp ([0] ++ xs) ([1] ++ ys) = .lt ∧ listCmp ([1] ++ ys) ([0,1] ++ zs) = .lt) : listCmp ([0] ++ xs) ([0,1] ++ zs) = .lt := transitListCmp ([0] ++ xs) ([1] ++ ys) ([0,1] ++ zs) h

-- lo_transit_2
example (xs ys zs : List Nat) (h : listCmp ([1] ++ xs) ([0,0] ++ ys) = .lt ∧ listCmp ([0,0] ++ ys) ([1,0] ++ zs) = .lt) : listCmp ([1] ++ xs) ([1,0] ++ zs) = .lt := transitListCmp ([1] ++ xs) ([0,0] ++ ys) ([1,0] ++ zs) h

-- lo_transit_3
example (xs ys zs : List Nat) (h : listCmp ([0,0] ++ xs) ([0,1] ++ ys) = .lt ∧ listCmp ([0,1] ++ ys) ([1208925819614629174706183] ++ zs) = .lt) : listCmp ([0,0] ++ xs) ([1208925819614629174706183] ++ zs) = .lt := transitListCmp ([0,0] ++ xs) ([0,1] ++ ys) ([1208925819614629174706183] ++ zs) h

-- lo_transit_4
example (xs ys zs : List Nat) (h : listCmp ([0,1] ++ xs) ([1,0] ++ ys) = .lt ∧ listCmp ([1,0] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ zs) = .lt) : listCmp ([0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ zs) = .lt := transitListCmp ([0,1] ++ xs) ([1,0] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ zs) h

-- lo_transit_5
example (xs ys zs : List Nat) (h : listCmp ([1,0] ++ xs) ([1208925819614629174706183] ++ ys) = .lt ∧ listCmp ([1208925819614629174706183] ++ ys) ([] ++ zs) = .lt) : listCmp ([1,0] ++ xs) ([] ++ zs) = .lt := transitListCmp ([1,0] ++ xs) ([1208925819614629174706183] ++ ys) ([] ++ zs) h

-- lo_transit_6
example (xs ys zs : List Nat) (h : listCmp ([1208925819614629174706183] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .lt ∧ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([0] ++ zs) = .lt) : listCmp ([1208925819614629174706183] ++ xs) ([0] ++ zs) = .lt := transitListCmp ([1208925819614629174706183] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([0] ++ zs) h

-- lo_transit_7
example (xs ys zs : List Nat) (h : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([] ++ ys) = .lt ∧ listCmp ([] ++ ys) ([1] ++ zs) = .lt) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1] ++ zs) = .lt := transitListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([] ++ ys) ([1] ++ zs) h

-- lo_transit_8
example (xs ys zs : List Nat) (h : listCmp ([] ++ xs) ([0] ++ ys) = .lt ∧ listCmp ([0] ++ ys) ([0,0] ++ zs) = .lt) : listCmp ([] ++ xs) ([0,0] ++ zs) = .lt := transitListCmp ([] ++ xs) ([0] ++ ys) ([0,0] ++ zs) h

-- lo_transit_9
example (xs ys zs : List Nat) (h : listCmp ([0] ++ xs) ([1] ++ ys) = .lt ∧ listCmp ([1] ++ ys) ([0,1] ++ zs) = .lt) : listCmp ([0] ++ xs) ([0,1] ++ zs) = .lt := transitListCmp ([0] ++ xs) ([1] ++ ys) ([0,1] ++ zs) h

-- lo_transit_10
example (xs ys zs : List Nat) (h : listCmp ([1] ++ xs) ([0,0] ++ ys) = .lt ∧ listCmp ([0,0] ++ ys) ([1,0] ++ zs) = .lt) : listCmp ([1] ++ xs) ([1,0] ++ zs) = .lt := transitListCmp ([1] ++ xs) ([0,0] ++ ys) ([1,0] ++ zs) h

-- lo_transit_11
example (xs ys zs : List Nat) (h : listCmp ([0,0] ++ xs) ([0,1] ++ ys) = .lt ∧ listCmp ([0,1] ++ ys) ([1208925819614629174706183] ++ zs) = .lt) : listCmp ([0,0] ++ xs) ([1208925819614629174706183] ++ zs) = .lt := transitListCmp ([0,0] ++ xs) ([0,1] ++ ys) ([1208925819614629174706183] ++ zs) h

-- lo_transit_12
example (xs ys zs : List Nat) (h : listCmp ([0,1] ++ xs) ([1,0] ++ ys) = .lt ∧ listCmp ([1,0] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ zs) = .lt) : listCmp ([0,1] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ zs) = .lt := transitListCmp ([0,1] ++ xs) ([1,0] ++ ys) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ zs) h

-- lo_transit_13
example (xs ys zs : List Nat) (h : listCmp ([1,0] ++ xs) ([1208925819614629174706183] ++ ys) = .lt ∧ listCmp ([1208925819614629174706183] ++ ys) ([] ++ zs) = .lt) : listCmp ([1,0] ++ xs) ([] ++ zs) = .lt := transitListCmp ([1,0] ++ xs) ([1208925819614629174706183] ++ ys) ([] ++ zs) h

-- lo_transit_14
example (xs ys zs : List Nat) (h : listCmp ([1208925819614629174706183] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) = .lt ∧ listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([0] ++ zs) = .lt) : listCmp ([1208925819614629174706183] ++ xs) ([0] ++ zs) = .lt := transitListCmp ([1208925819614629174706183] ++ xs) ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ ys) ([0] ++ zs) h

-- lo_transit_15
example (xs ys zs : List Nat) (h : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([] ++ ys) = .lt ∧ listCmp ([] ++ ys) ([1] ++ zs) = .lt) : listCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([1] ++ zs) = .lt := transitListCmp ([0,0,0,0,0,0,0,0,0,0,0,0,1] ++ xs) ([] ++ ys) ([1] ++ zs) h


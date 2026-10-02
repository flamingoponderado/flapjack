import Flapjack.Compiler.Backend.WordToStack.Proofs.SortedAList
open Flapjack Flapjack.WordToStackProofs Flapjack.Compiler.Backend.WordToStack
set_option maxRecDepth 8192

-- Test-only decision procedure for the original adjacent-key predicate.
local instance {α : Type} (xs : List (Nat × α)) : Decidable (descendingKeys xs) := by
  unfold descendingKeys
  infer_instance

-- sa_output_0
example : sptToAList (sptFromAList ([] : List (Nat × Nat))) = [] := by decide +kernel

-- sa_member_0_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((0,11) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((0,22) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((0,33) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((1,11) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((1,22) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((1,33) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((2,11) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((2,22) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((2,33) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((3,11) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((3,22) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((3,33) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((7,11) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((7,22) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((7,33) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((99,11) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((99,22) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_0_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([] : List (Nat × Nat)))), decide ((99,33) ∈ ([] : List (Nat × Nat))), decide (([] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_output_1
example : sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat))) = [(0,11)] := by decide +kernel

-- sa_member_1_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_1_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_1_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(0,11)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(0,11)] : List (Nat × Nat))), decide (([(0,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_output_2
example : sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat))) = [(1,22)] := by decide +kernel

-- sa_member_2_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_2_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_2_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(1,22)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(1,22)] : List (Nat × Nat))), decide (([(1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(1,22)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_output_3
example : sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))) = [(7,11), (3,22), (1,33), (0,44)] := by decide +kernel

-- sa_member_3_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_3_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_3_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_3_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_3_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat))), decide (([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (3,22), (1,33), (0,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_output_4
example : sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))) = [(3,44), (1,22), (0,11), (2,33)] := by decide +kernel

-- sa_member_4_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (true, true, true, false) := by decide +kernel

-- sa_member_4_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (true, true, true, false) := by decide +kernel

-- sa_member_4_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (true, true, true, false) := by decide +kernel

-- sa_member_4_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_member_4_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat))), decide (([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (1,22), (2,33), (3,44)] : List (Nat × Nat)))) = (false, false, true, false) := by decide +kernel

-- sa_output_5
example : sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat))) = [(3,11)] := by decide +kernel

-- sa_member_5_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (true, true, false, false) := by decide +kernel

-- sa_member_5_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, true, false, false) := by decide +kernel

-- sa_member_5_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_5_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(3,11), (3,22)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(3,11), (3,22)] : List (Nat × Nat))), decide (([(3,11), (3,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,11), (3,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_output_6
example : sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat))) = [(3,22)] := by decide +kernel

-- sa_member_6_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, true, false, false) := by decide +kernel

-- sa_member_6_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (true, true, false, false) := by decide +kernel

-- sa_member_6_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_6_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(3,22), (3,11)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(3,22), (3,11)] : List (Nat × Nat))), decide (([(3,22), (3,11)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(3,22), (3,11)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_output_7
example : sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat))) = [(0,22), (2,11)] := by decide +kernel

-- sa_member_7_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (true, true, false, false) := by decide +kernel

-- sa_member_7_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (true, true, false, false) := by decide +kernel

-- sa_member_7_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, true, false, false) := by decide +kernel

-- sa_member_7_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_7_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(2,11), (0,22), (2,33)] : List (Nat × Nat))), decide (([(2,11), (0,22), (2,33)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(2,11), (0,22), (2,33)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_output_8
example : sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))) = [(7,11), (1,44), (4,22), (2,33)] := by decide +kernel

-- sa_member_8_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_8_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_8_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_8_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat))), decide (([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(7,11), (4,22), (2,33), (1,44)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_output_9
example : sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))) = [(31,11), (15,22), (7,33), (3,44), (1,55)] := by decide +kernel

-- sa_member_9_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_9_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_9_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat))), decide (([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(31,11), (15,22), (7,33), (3,44), (1,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_output_10
example : sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))) = [(7,33), (99,11), (0,55), (80,22), (2,44)] := by decide +kernel

-- sa_member_10_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_10_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (true, true, true, true) := by decide +kernel

-- sa_member_10_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_member_10_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat))), decide (([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(99,11), (80,22), (7,33), (2,44), (0,55)] : List (Nat × Nat)))) = (false, false, true, true) := by decide +kernel

-- sa_output_11
example : sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat))) = [(1,22), (0,11)] := by decide +kernel

-- sa_member_11_0_11
example : (decide ((0,11) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((0,11) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (true, true, false, false) := by decide +kernel

-- sa_member_11_0_22
example : (decide ((0,22) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((0,22) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_0_33
example : (decide ((0,33) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((0,33) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_1_11
example : (decide ((1,11) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((1,11) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_1_22
example : (decide ((1,22) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((1,22) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (true, true, false, false) := by decide +kernel

-- sa_member_11_1_33
example : (decide ((1,33) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((1,33) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_2_11
example : (decide ((2,11) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((2,11) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_2_22
example : (decide ((2,22) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((2,22) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_2_33
example : (decide ((2,33) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((2,33) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_3_11
example : (decide ((3,11) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((3,11) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_3_22
example : (decide ((3,22) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((3,22) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_3_33
example : (decide ((3,33) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((3,33) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_7_11
example : (decide ((7,11) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((7,11) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_7_22
example : (decide ((7,22) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((7,22) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_7_33
example : (decide ((7,33) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((7,33) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_99_11
example : (decide ((99,11) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((99,11) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_99_22
example : (decide ((99,22) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((99,22) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

-- sa_member_11_99_33
example : (decide ((99,33) ∈ sptToAList (sptFromAList ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))), decide ((99,33) ∈ ([(0,11), (0,11), (1,22)] : List (Nat × Nat))), decide (([(0,11), (0,11), (1,22)] : List (Nat × Nat)).map Prod.fst).Nodup, decide (descendingKeys ([(0,11), (0,11), (1,22)] : List (Nat × Nat)))) = (false, false, false, false) := by decide +kernel

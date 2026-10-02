import Flapjack.Compiler.Backend.WordToStack.Proofs.ExtractLabelsHelpers

/-! Independent original ordered-list observations and full helper applications.
Regression evidence does not establish cross-language equivalence. -/
namespace Flapjack.Test.WordToStackExtractLabelsHelpersParity
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.WordToStack.Native
open ExtractLabelsHelpers

-- elh_1_move_0_skip
example : extractLabels (stackMoveNative 0 1180591620717411303424 9 4 (.skip) : HolProg 1) = [] := by rfl

-- elh_1_move_0_labels
example : extractLabels (stackMoveNative 0 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_aux_0
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 1) = [] := by rfl

-- elh_1_alloc_0
example : extractLabels (stackMoveNative 0 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 1) = [] := by rfl

-- elh_1_move_1_skip
example : extractLabels (stackMoveNative 1 1180591620717411303424 9 4 (.skip) : HolProg 1) = [] := by rfl

-- elh_1_move_1_labels
example : extractLabels (stackMoveNative 1 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_aux_1
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 1) = [] := by rfl

-- elh_1_alloc_1
example : extractLabels (stackMoveNative 1 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 1) = [] := by rfl

-- elh_1_move_3_skip
example : extractLabels (stackMoveNative 3 1180591620717411303424 9 4 (.skip) : HolProg 1) = [] := by rfl

-- elh_1_move_3_labels
example : extractLabels (stackMoveNative 3 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_aux_3
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 1) = [] := by rfl

-- elh_1_alloc_3
example : extractLabels (stackMoveNative 3 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 1) = [] := by rfl

-- elh_1_ret_0_0_0
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_0_0_3
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_0_0_7
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_0_1_0
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_0_1_3
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_0_1_7
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_1_0_0
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_1_0_3
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_1_0_7
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_1_1_0
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_1_1_3
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_ret_1_1_7
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 1) = [(7,8), (9,10)] := by rfl

-- elh_1_load_24
example : extractLabels (wStackLoadNative [] .skip : HolProg 1) = [] := by rfl

-- elh_1_load_25
example : extractLabels (wStackLoadNative [(1,2)] .skip : HolProg 1) = [] := by rfl

-- elh_1_load_26
example : extractLabels (wStackLoadNative [(1,2),(3,4),(1,2)] .skip : HolProg 1) = [] := by rfl

-- elh_8_move_0_skip
example : extractLabels (stackMoveNative 0 1180591620717411303424 9 4 (.skip) : HolProg 8) = [] := by rfl

-- elh_8_move_0_labels
example : extractLabels (stackMoveNative 0 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_aux_0
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 8) = [] := by rfl

-- elh_8_alloc_0
example : extractLabels (stackMoveNative 0 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 8) = [] := by rfl

-- elh_8_move_1_skip
example : extractLabels (stackMoveNative 1 1180591620717411303424 9 4 (.skip) : HolProg 8) = [] := by rfl

-- elh_8_move_1_labels
example : extractLabels (stackMoveNative 1 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_aux_1
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 8) = [] := by rfl

-- elh_8_alloc_1
example : extractLabels (stackMoveNative 1 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 8) = [] := by rfl

-- elh_8_move_3_skip
example : extractLabels (stackMoveNative 3 1180591620717411303424 9 4 (.skip) : HolProg 8) = [] := by rfl

-- elh_8_move_3_labels
example : extractLabels (stackMoveNative 3 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_aux_3
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 8) = [] := by rfl

-- elh_8_alloc_3
example : extractLabels (stackMoveNative 3 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 8) = [] := by rfl

-- elh_8_ret_0_0_0
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_0_0_3
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_0_0_7
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_0_1_0
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_0_1_3
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_0_1_7
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_1_0_0
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_1_0_3
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_1_0_7
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_1_1_0
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_1_1_3
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_ret_1_1_7
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 8) = [(7,8), (9,10)] := by rfl

-- elh_8_load_51
example : extractLabels (wStackLoadNative [] .skip : HolProg 8) = [] := by rfl

-- elh_8_load_52
example : extractLabels (wStackLoadNative [(1,2)] .skip : HolProg 8) = [] := by rfl

-- elh_8_load_53
example : extractLabels (wStackLoadNative [(1,2),(3,4),(1,2)] .skip : HolProg 8) = [] := by rfl

-- elh_64_move_0_skip
example : extractLabels (stackMoveNative 0 1180591620717411303424 9 4 (.skip) : HolProg 64) = [] := by rfl

-- elh_64_move_0_labels
example : extractLabels (stackMoveNative 0 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_aux_0
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 64) = [] := by rfl

-- elh_64_alloc_0
example : extractLabels (stackMoveNative 0 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 64) = [] := by rfl

-- elh_64_move_1_skip
example : extractLabels (stackMoveNative 1 1180591620717411303424 9 4 (.skip) : HolProg 64) = [] := by rfl

-- elh_64_move_1_labels
example : extractLabels (stackMoveNative 1 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_aux_1
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 64) = [] := by rfl

-- elh_64_alloc_1
example : extractLabels (stackMoveNative 1 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 64) = [] := by rfl

-- elh_64_move_3_skip
example : extractLabels (stackMoveNative 3 1180591620717411303424 9 4 (.skip) : HolProg 64) = [] := by rfl

-- elh_64_move_3_labels
example : extractLabels (stackMoveNative 3 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_aux_3
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 64) = [] := by rfl

-- elh_64_alloc_3
example : extractLabels (stackMoveNative 3 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 64) = [] := by rfl

-- elh_64_ret_0_0_0
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_0_0_3
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_0_0_7
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_0_1_0
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_0_1_3
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_0_1_7
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_1_0_0
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_1_0_3
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_1_0_7
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_1_1_0
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_1_1_3
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_ret_1_1_7
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 64) = [(7,8), (9,10)] := by rfl

-- elh_64_load_78
example : extractLabels (wStackLoadNative [] .skip : HolProg 64) = [] := by rfl

-- elh_64_load_79
example : extractLabels (wStackLoadNative [(1,2)] .skip : HolProg 64) = [] := by rfl

-- elh_64_load_80
example : extractLabels (wStackLoadNative [(1,2),(3,4),(1,2)] .skip : HolProg 64) = [] := by rfl

-- elh_80_move_0_skip
example : extractLabels (stackMoveNative 0 1180591620717411303424 9 4 (.skip) : HolProg 80) = [] := by rfl

-- elh_80_move_0_labels
example : extractLabels (stackMoveNative 0 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_aux_0
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 80) = [] := by rfl

-- elh_80_alloc_0
example : extractLabels (stackMoveNative 0 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 80) = [] := by rfl

-- elh_80_move_1_skip
example : extractLabels (stackMoveNative 1 1180591620717411303424 9 4 (.skip) : HolProg 80) = [] := by rfl

-- elh_80_move_1_labels
example : extractLabels (stackMoveNative 1 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_aux_1
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 80) = [] := by rfl

-- elh_80_alloc_1
example : extractLabels (stackMoveNative 1 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 80) = [] := by rfl

-- elh_80_move_3_skip
example : extractLabels (stackMoveNative 3 1180591620717411303424 9 4 (.skip) : HolProg 80) = [] := by rfl

-- elh_80_move_3_labels
example : extractLabels (stackMoveNative 3 1180591620717411303424 9 4 (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_aux_3
example : extractLabels (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 80) = [] := by rfl

-- elh_80_alloc_3
example : extractLabels (stackMoveNative 3 0 9 4 (.stackAlloc 1180591620717411303424) : HolProg 80) = [] := by rfl

-- elh_80_ret_0_0_0
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_0_0_3
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_0_0_7
example : extractLabels (copyRetNative false false (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_0_1_0
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_0_1_3
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_0_1_7
example : extractLabels (copyRetNative false true (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_1_0_0
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_1_0_3
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_1_0_7
example : extractLabels (copyRetNative true false (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_1_1_0
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_1_1_3
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([0,1,2] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_ret_1_1_7
example : extractLabels (copyRetNative true true (4,1180591620717411303424,(0 : Nat)) ([0,1,2,3,4,5,6] : List Nat) (.call (some (.skip,0,7,8)) (.inr 0) (some (.skip,9,10))) : HolProg 80) = [(7,8), (9,10)] := by rfl

-- elh_80_load_105
example : extractLabels (wStackLoadNative [] .skip : HolProg 80) = [] := by rfl

-- elh_80_load_106
example : extractLabels (wStackLoadNative [(1,2)] .skip : HolProg 80) = [] := by rfl

-- elh_80_load_107
example : extractLabels (wStackLoadNative [(1,2),(3,4),(1,2)] .skip : HolProg 80) = [] := by rfl

example {width : Nat} [NeZero width] (n a b c : Nat) (p : HolProg width)
    (h : extractLabels p = []) : extractLabels (stackMoveNative n a b c p) = [] :=
  stackMoveNoLabs n a b c p h
example {width : Nat} [NeZero width] (k f n : Nat) :
    extractLabels (copyRetAuxNative (width := width) k f n) = [] := copyRetAuxLabels k f n
example {width : Nat} [NeZero width] {β γ : Type}
    (perf b : Bool) (kf : Nat × Nat × γ) (vs : List β) (kont : HolProg width) :
    extractLabels (copyRetNative perf b kf vs kont) = extractLabels kont :=
  copyRetLabels perf b kf vs kont
example {width : Nat} [NeZero width] (xs : List (Nat × Nat)) :
    extractLabels (wStackLoadNative xs (.skip : HolProg width)) = [] := stackLoadSkipLabels xs
example {width : Nat} [NeZero width] (n start offset i k : Nat) :
    extractLabels (stackMoveNative n start offset i (.stackAlloc k : HolProg width)) = [] :=
  stackMoveAllocLabels n start offset i k

def runChecks : IO Bool := do
  IO.println "PASS original ordered-label helpers (108 kernel rows, five full theorem applications)"
  pure true
end Flapjack.Test.WordToStackExtractLabelsHelpersParity

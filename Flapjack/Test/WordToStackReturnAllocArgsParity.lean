import Flapjack.Compiler.Backend.WordToStack.Proofs.ReturnAllocArgs

namespace Flapjack.Test.WordToStackReturnAllocArgsParity

open Flapjack.Compiler.Backend.WordToStack.Native

open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps

open Flapjack.WordToStackProofs

/- Original regression boundary: word_to_stack_return_alloc_args_probe.out. Complete original proofs and same-input predicate pairs; not cross-language equivalence. -/

-- raa_move_1_0_0
example : (allocArg (.skip : HolProg 1) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 1)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_0_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 1)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_0_2
example : (allocArg (.alloc 2 : HolProg 1) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 1)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_0_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 1) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 1)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_0_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 1) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 1)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_1_0
example : (allocArg (.skip : HolProg 1) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 1)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_1_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 1)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_1_2
example : (allocArg (.alloc 2 : HolProg 1) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 1)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_1_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 1) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 1)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_1_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 1) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 1)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_4_0
example : (allocArg (.skip : HolProg 1) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 1)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_4_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 1)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_4_2
example : (allocArg (.alloc 2 : HolProg 1) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 1)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_4_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 1) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 1)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_4_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_1_4_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 1) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 1)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_ret_1_0_0_0_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_0_1_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_0_2_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_1_0_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_1_1_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_1_2_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_0_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_0_0_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_0_1_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_0_2_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_1_0_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_1_1_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_1_2_1
example : (allocArg (.alloc 1 : HolProg 1) ↔ True) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 1)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_1_1_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1) ↔ False) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 1)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_move_2_0_0
example : (allocArg (.skip : HolProg 2) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 2)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_0_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 2)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_0_2
example : (allocArg (.alloc 2 : HolProg 2) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 2)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_0_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 2) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 2)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_0_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 2) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 2)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_1_0
example : (allocArg (.skip : HolProg 2) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 2)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_1_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 2)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_1_2
example : (allocArg (.alloc 2 : HolProg 2) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 2)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_1_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 2) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 2)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_1_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 2) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 2)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_4_0
example : (allocArg (.skip : HolProg 2) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 2)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_4_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 2)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_4_2
example : (allocArg (.alloc 2 : HolProg 2) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 2)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_4_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 2) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 2)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_4_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_2_4_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 2) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 2)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_ret_2_0_0_0_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_0_1_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_0_2_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_1_0_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_1_1_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_1_2_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_0_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_0_0_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_0_1_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_0_2_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_1_0_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_1_1_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_1_2_1
example : (allocArg (.alloc 1 : HolProg 2) ↔ True) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 2)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_2_1_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2) ↔ False) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 2)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_move_8_0_0
example : (allocArg (.skip : HolProg 8) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 8)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_0_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 8)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_0_2
example : (allocArg (.alloc 2 : HolProg 8) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 8)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_0_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 8) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 8)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_0_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 8) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 8)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_1_0
example : (allocArg (.skip : HolProg 8) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 8)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_1_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 8)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_1_2
example : (allocArg (.alloc 2 : HolProg 8) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 8)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_1_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 8) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 8)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_1_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 8) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 8)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_4_0
example : (allocArg (.skip : HolProg 8) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 8)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_4_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 8)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_4_2
example : (allocArg (.alloc 2 : HolProg 8) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 8)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_4_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 8) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 8)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_4_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_8_4_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 8) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 8)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_ret_8_0_0_0_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_0_1_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_0_2_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_1_0_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_1_1_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_1_2_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_0_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_0_0_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_0_1_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_0_2_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_1_0_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_1_1_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_1_2_1
example : (allocArg (.alloc 1 : HolProg 8) ↔ True) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 8)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_8_1_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8) ↔ False) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 8)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_move_64_0_0
example : (allocArg (.skip : HolProg 64) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 64)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_0_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 64)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_0_2
example : (allocArg (.alloc 2 : HolProg 64) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 64)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_0_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 64) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 64)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_0_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 64) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 64)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_1_0
example : (allocArg (.skip : HolProg 64) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 64)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_1_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 64)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_1_2
example : (allocArg (.alloc 2 : HolProg 64) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 64)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_1_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 64) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 64)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_1_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 64) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 64)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_4_0
example : (allocArg (.skip : HolProg 64) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 64)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_4_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 64)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_4_2
example : (allocArg (.alloc 2 : HolProg 64) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 64)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_4_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 64) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 64)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_4_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_64_4_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 64) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 64)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_ret_64_0_0_0_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_0_1_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_0_2_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_1_0_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_1_1_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_1_2_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_0_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_0_0_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_0_1_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_0_2_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_1_0_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_1_1_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_1_2_1
example : (allocArg (.alloc 1 : HolProg 64) ↔ True) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 64)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_64_1_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64) ↔ False) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 64)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_move_80_0_0
example : (allocArg (.skip : HolProg 80) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 80)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_0_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 80)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_0_2
example : (allocArg (.alloc 2 : HolProg 80) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 80)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_0_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 80) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 80)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_0_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 80) ↔ True) ∧ (allocArg (stackMoveNative 0 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 80)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_1_0
example : (allocArg (.skip : HolProg 80) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 80)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_1_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 80)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_1_2
example : (allocArg (.alloc 2 : HolProg 80) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 80)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_1_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 80) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 80)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_1_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 80) ↔ True) ∧ (allocArg (stackMoveNative 1 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 80)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_4_0
example : (allocArg (.skip : HolProg 80) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.skip : HolProg 80)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_4_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 1 : HolProg 80)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_4_2
example : (allocArg (.alloc 2 : HolProg 80) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.alloc 2 : HolProg 80)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_4_3
example : (allocArg (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 80) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.seq (.alloc 1) (.loop (.alloc 2)) : HolProg 80)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_4_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  simp [stackMoveNative, allocArg]

-- raa_move_80_4_5
example : (allocArg (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 80) ↔ True) ∧ (allocArg (stackMoveNative 4 1180591620717411303425 0 1180591620717411303427 (.call (some (.alloc 1,0,1,2)) (.inl 0) (some (.alloc 1,3,4)) : HolProg 80)) ↔ True) := by
  simp [stackMoveNative, allocArg]

-- raa_ret_80_0_0_0_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative false false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_0_1_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative false false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_0_2_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative false false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_1_0_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative false true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_1_1_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative false true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_1_2_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_0_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative false true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_0_0_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_0_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative true false (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_0_1_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_0_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative true false (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_0_2_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_0_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative true false (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_1_0_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_1_0_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative true true (0,0,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_1_1_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_1_1_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative true true (4,0,false) ([true,false] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_1_2_1
example : (allocArg (.alloc 1 : HolProg 80) ↔ True) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.alloc 1 : HolProg 80)) ↔ True) := by
  rw [allocArgCopyRet]
  simp [allocArg]

-- raa_ret_80_1_1_2_4
example : (allocArg (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80) ↔ False) ∧ (allocArg (copyRetNative true true (1,1180591620717411303424,true) ([true,false,true] : List Bool) (.call none (.inl 0) (some (.alloc 2,3,4)) : HolProg 80)) ↔ False) := by
  rw [allocArgCopyRet]
  simp [allocArg]

example {width : Nat} [NeZero width] (n st off i : Nat) (p : HolProg width) (h : allocArg p) : allocArg (stackMoveNative n st off i p) := stackMoveAllocArg n st off i p h

example {width : Nat} [NeZero width] (k f n : Nat) : allocArg (copyRetAuxNative (width := width) k f n) := allocArgCopyRetAux k f n

example {width : Nat} [NeZero width] {β γ : Type} (perf b : Bool) (kf : Nat × Nat × γ) (vs : List β) (kont : HolProg width) : allocArg (copyRetNative perf b kf vs kont) ↔ allocArg kont := allocArgCopyRet perf b kf vs kont

end Flapjack.Test.WordToStackReturnAllocArgsParity

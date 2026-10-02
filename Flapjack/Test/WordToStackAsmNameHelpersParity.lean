import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameHelpers

namespace Flapjack.Test.WordToStackAsmNameHelpersParity
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
/- Fresh original five literal proof replays, original inferred shared word
carrier and230 naming observations. Underflow breaks only nonzero wLive cases;
other helpers retain their original unconditional statement shapes. -/

-- anh_1_80_dest_direct=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 80 × Sum Nat Nat).1) := by cbv

-- anh_1_80_dest_empty=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 80 × Sum Nat Nat).1) := by cbv

-- anh_1_80_dest_reg=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 80 × Sum Nat Nat).1) := by cbv

-- anh_1_80_dest_spill=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 80 × Sum Nat Nat).1) := by cbv

-- anh_1_80_move_0_0=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_0_1=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_1_0=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_1_1=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_3_0=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_3_1=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_aux_0=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 80) := by cbv

-- anh_1_80_aux_1=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 80) := by cbv

-- anh_1_80_aux_3=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 80) := by cbv

-- anh_1_80_ret_0_0=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_0_0_perf=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_0_1=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_0_1_perf=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_1_0=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_1_0_perf=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_1_1=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_1_1_perf=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_80_1_dest_direct=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 1 × Sum Nat Nat).1) := by cbv

-- anh_80_1_dest_empty=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 1 × Sum Nat Nat).1) := by cbv

-- anh_80_1_dest_reg=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 1 × Sum Nat Nat).1) := by cbv

-- anh_80_1_dest_spill=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 1 × Sum Nat Nat).1) := by cbv

-- anh_80_1_move_0_0=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_0_1=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_1_0=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_1_1=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_3_0=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_3_1=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_aux_0=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 1) := by cbv

-- anh_80_1_aux_1=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 1) := by cbv

-- anh_80_1_aux_3=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 1) := by cbv

-- anh_80_1_ret_0_0=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_0_0_perf=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_0_1=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_0_1_perf=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_1_0=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_1_0_perf=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_1_1=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_1_1_perf=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_2_64_dest_direct=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 64 × Sum Nat Nat).1) := by cbv

-- anh_2_64_dest_empty=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 64 × Sum Nat Nat).1) := by cbv

-- anh_2_64_dest_reg=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 64 × Sum Nat Nat).1) := by cbv

-- anh_2_64_dest_spill=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 64 × Sum Nat Nat).1) := by cbv

-- anh_2_64_move_0_0=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_0_1=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_1_0=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_1_1=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_3_0=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_3_1=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_aux_0=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 64) := by cbv

-- anh_2_64_aux_1=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 64) := by cbv

-- anh_2_64_aux_3=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 64) := by cbv

-- anh_2_64_ret_0_0=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_0_0_perf=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_0_1=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_0_1_perf=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_1_0=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_1_0_perf=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_1_1=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_1_1_perf=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_64_2_dest_direct=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 2 × Sum Nat Nat).1) := by cbv

-- anh_64_2_dest_empty=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 2 × Sum Nat Nat).1) := by cbv

-- anh_64_2_dest_reg=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 2 × Sum Nat Nat).1) := by cbv

-- anh_64_2_dest_spill=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 2 × Sum Nat Nat).1) := by cbv

-- anh_64_2_move_0_0=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_0_1=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_1_0=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_1_1=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_3_0=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_3_1=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_aux_0=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 2) := by cbv

-- anh_64_2_aux_1=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 2) := by cbv

-- anh_64_2_aux_3=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 2) := by cbv

-- anh_64_2_ret_0_0=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_0_0_perf=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_0_1=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_0_1_perf=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_1_0=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_1_0_perf=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_1_1=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_1_1_perf=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_8_8_dest_direct=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 8 × Sum Nat Nat).1) := by cbv

-- anh_8_8_dest_empty=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 8 × Sum Nat Nat).1) := by cbv

-- anh_8_8_dest_reg=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 8 × Sum Nat Nat).1) := by cbv

-- anh_8_8_dest_spill=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 8 × Sum Nat Nat).1) := by cbv

-- anh_8_8_move_0_0=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_0_1=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_1_0=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_1_1=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_3_0=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_3_1=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_aux_0=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 8) := by cbv

-- anh_8_8_aux_1=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 8) := by cbv

-- anh_8_8_aux_3=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 8) := by cbv

-- anh_8_8_ret_0_0=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_0_0_perf=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_0_1=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_0_1_perf=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_1_0=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_1_0_perf=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_1_1=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_1_1_perf=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 8, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_1_80_live_0=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 80 8,BitVec.ofNat 80 2],99) (4,0,3) : HolProg 80 × (AppList (BitVec 80) × Nat)).1) := by cbv

-- anh_1_80_live_7=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 80 8,BitVec.ofNat 80 2],99) (4,7,3) : HolProg 80 × (AppList (BitVec 80) × Nat)).1) := by cbv

-- anh_80_1_live_0=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 1 8,BitVec.ofNat 1 2],99) (4,0,3) : HolProg 1 × (AppList (BitVec 1) × Nat)).1) := by cbv

-- anh_80_1_live_7=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 1 8,BitVec.ofNat 1 2],99) (4,7,3) : HolProg 1 × (AppList (BitVec 1) × Nat)).1) := by cbv

-- anh_2_64_live_0=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 64 8,BitVec.ofNat 64 2],99) (4,0,3) : HolProg 64 × (AppList (BitVec 64) × Nat)).1) := by cbv

-- anh_2_64_live_7=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 64 8,BitVec.ofNat 64 2],99) (4,7,3) : HolProg 64 × (AppList (BitVec 64) × Nat)).1) := by cbv

-- anh_64_2_live_0=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 2 8,BitVec.ofNat 2 2],99) (4,0,3) : HolProg 2 × (AppList (BitVec 2) × Nat)).1) := by cbv

-- anh_64_2_live_7=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 2 8,BitVec.ofNat 2 2],99) (4,7,3) : HolProg 2 × (AppList (BitVec 2) × Nat)).1) := by cbv

-- anh_8_8_live_0=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 8 8,BitVec.ofNat 8 2],99) (4,0,3) : HolProg 8 × (AppList (BitVec 8) × Nat)).1) := by cbv

-- anh_8_8_live_7=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 8, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 8 8,BitVec.ofNat 8 2],99) (4,7,3) : HolProg 8 × (AppList (BitVec 8) × Nat)).1) := by cbv

-- anh_1_80_dest_direct_underflow=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 80 × Sum Nat Nat).1) := by cbv

-- anh_1_80_dest_empty_underflow=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 80 × Sum Nat Nat).1) := by cbv

-- anh_1_80_dest_reg_underflow=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 80 × Sum Nat Nat).1) := by cbv

-- anh_1_80_dest_spill_underflow=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 80 × Sum Nat Nat).1) := by cbv

-- anh_1_80_move_0_0_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_0_1_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_1_0_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_1_1_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_3_0_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_move_3_1_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_aux_0_underflow=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 80) := by cbv

-- anh_1_80_aux_1_underflow=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 80) := by cbv

-- anh_1_80_aux_3_underflow=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 80) := by cbv

-- anh_1_80_ret_0_0_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_0_0_perf_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_0_1_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_0_1_perf_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_1_0_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_1_0_perf_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_1_1_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_1_80_ret_1_1_perf_underflow=T
example (c : AsmConfigExact 80) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 80)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 80)) := by cbv <;> simp

-- anh_80_1_dest_direct_underflow=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 1 × Sum Nat Nat).1) := by cbv

-- anh_80_1_dest_empty_underflow=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 1 × Sum Nat Nat).1) := by cbv

-- anh_80_1_dest_reg_underflow=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 1 × Sum Nat Nat).1) := by cbv

-- anh_80_1_dest_spill_underflow=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 1 × Sum Nat Nat).1) := by cbv

-- anh_80_1_move_0_0_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_0_1_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_1_0_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_1_1_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_3_0_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_move_3_1_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_aux_0_underflow=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 1) := by cbv

-- anh_80_1_aux_1_underflow=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 1) := by cbv

-- anh_80_1_aux_3_underflow=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 1) := by cbv

-- anh_80_1_ret_0_0_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_0_0_perf_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_0_1_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_0_1_perf_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_1_0_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_1_0_perf_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_1_1_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_80_1_ret_1_1_perf_underflow=T
example (c : AsmConfigExact 1) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 1)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 1)) := by cbv <;> simp

-- anh_2_64_dest_direct_underflow=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 64 × Sum Nat Nat).1) := by cbv

-- anh_2_64_dest_empty_underflow=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 64 × Sum Nat Nat).1) := by cbv

-- anh_2_64_dest_reg_underflow=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 64 × Sum Nat Nat).1) := by cbv

-- anh_2_64_dest_spill_underflow=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 64 × Sum Nat Nat).1) := by cbv

-- anh_2_64_move_0_0_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_0_1_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_1_0_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_1_1_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_3_0_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_move_3_1_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_aux_0_underflow=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 64) := by cbv

-- anh_2_64_aux_1_underflow=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 64) := by cbv

-- anh_2_64_aux_3_underflow=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 64) := by cbv

-- anh_2_64_ret_0_0_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_0_0_perf_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_0_1_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_0_1_perf_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_1_0_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_1_0_perf_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_1_1_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_2_64_ret_1_1_perf_underflow=T
example (c : AsmConfigExact 64) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 64)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 64)) := by cbv <;> simp

-- anh_64_2_dest_direct_underflow=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 2 × Sum Nat Nat).1) := by cbv

-- anh_64_2_dest_empty_underflow=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 2 × Sum Nat Nat).1) := by cbv

-- anh_64_2_dest_reg_underflow=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 2 × Sum Nat Nat).1) := by cbv

-- anh_64_2_dest_spill_underflow=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 2 × Sum Nat Nat).1) := by cbv

-- anh_64_2_move_0_0_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_0_1_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_1_0_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_1_1_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_3_0_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_move_3_1_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_aux_0_underflow=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 2) := by cbv

-- anh_64_2_aux_1_underflow=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 2) := by cbv

-- anh_64_2_aux_3_underflow=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 2) := by cbv

-- anh_64_2_ret_0_0_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_0_0_perf_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_0_1_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_0_1_perf_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_1_0_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_1_0_perf_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_1_1_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_64_2_ret_1_1_perf_underflow=T
example (c : AsmConfigExact 2) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 2)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 2)) := by cbv <;> simp

-- anh_8_8_dest_direct_underflow=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (some 1180591620717411303424) [] (4,1180591620717411303424,0) : HolProg 8 × Sum Nat Nat).1) := by cbv

-- anh_8_8_dest_empty_underflow=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [] (4,1180591620717411303424,0) : HolProg 8 × Sum Nat Nat).1) := by cbv

-- anh_8_8_dest_reg_underflow=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,4] (4,1180591620717411303424,0) : HolProg 8 × Sum Nat Nat).1) := by cbv

-- anh_8_8_dest_spill_underflow=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((callDestNative (none) [2,1180591620717411303424] (4,1180591620717411303424,0) : HolProg 8 × Sum Nat Nat).1) := by cbv

-- anh_8_8_move_0_0_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_0_1_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 0 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_1_0_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_1_1_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 1 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_3_0_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_move_3_1_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (stackMoveNative 3 1180591620717411303424 9 4 (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_aux_0_underflow=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 0 : HolProg 8) := by cbv

-- anh_8_8_aux_1_underflow=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 1 : HolProg 8) := by cbv

-- anh_8_8_aux_3_underflow=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetAuxNative 4 1180591620717411303424 3 : HolProg 8) := by cbv

-- anh_8_8_ret_0_0_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_0_0_perf_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_0_1_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_0_1_perf_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true false (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_1_0_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_1_0_perf_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.skip : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.skip : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_1_1_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative false true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_8_8_ret_1_1_perf_underflow=T
example (c : AsmConfigExact 8) : (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (copyRetNative true true (4,1180591620717411303424,()) ([1,2,3,4,5,6] : List Nat) (.get 6 .currHeap : HolProg 8)) ↔ stackAsmName {c with regCount := 0, avoidRegs := [0,1]} (.get 6 .currHeap : HolProg 8)) := by cbv <;> simp

-- anh_1_80_live_0_underflow=T
example (c : AsmConfigExact 80) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 80 8,BitVec.ofNat 80 2],99) (4,0,3) : HolProg 80 × (AppList (BitVec 80) × Nat)).1) := by cbv

-- anh_1_80_live_7_underflow=F
example (c : AsmConfigExact 80) : ¬ (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 80 8,BitVec.ofNat 80 2],99) (4,7,3) : HolProg 80 × (AppList (BitVec 80) × Nat)).1)) := by cbv

-- anh_80_1_live_0_underflow=T
example (c : AsmConfigExact 1) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 1 8,BitVec.ofNat 1 2],99) (4,0,3) : HolProg 1 × (AppList (BitVec 1) × Nat)).1) := by cbv

-- anh_80_1_live_7_underflow=F
example (c : AsmConfigExact 1) : ¬ (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 1 8,BitVec.ofNat 1 2],99) (4,7,3) : HolProg 1 × (AppList (BitVec 1) × Nat)).1)) := by cbv

-- anh_2_64_live_0_underflow=T
example (c : AsmConfigExact 64) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 64 8,BitVec.ofNat 64 2],99) (4,0,3) : HolProg 64 × (AppList (BitVec 64) × Nat)).1) := by cbv

-- anh_2_64_live_7_underflow=F
example (c : AsmConfigExact 64) : ¬ (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 64 8,BitVec.ofNat 64 2],99) (4,7,3) : HolProg 64 × (AppList (BitVec 64) × Nat)).1)) := by cbv

-- anh_64_2_live_0_underflow=T
example (c : AsmConfigExact 2) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 2 8,BitVec.ofNat 2 2],99) (4,0,3) : HolProg 2 × (AppList (BitVec 2) × Nat)).1) := by cbv

-- anh_64_2_live_7_underflow=F
example (c : AsmConfigExact 2) : ¬ (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 2 8,BitVec.ofNat 2 2],99) (4,7,3) : HolProg 2 × (AppList (BitVec 2) × Nat)).1)) := by cbv

-- anh_8_8_live_0_underflow=T
example (c : AsmConfigExact 8) : stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 8 8,BitVec.ofNat 8 2],99) (4,0,3) : HolProg 8 × (AppList (BitVec 8) × Nat)).1) := by cbv

-- anh_8_8_live_7_underflow=F
example (c : AsmConfigExact 8) : ¬ (stackAsmName {c with regCount := 0, avoidRegs := [0,1]} ((wLiveNative (.ln,.ln) (.list [BitVec.ofNat 8 8,BitVec.ofNat 8 2],99) (4,7,3) : HolProg 8 × (AppList (BitVec 8) × Nat)).1)) := by cbv

example {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (p : HolProg width) (perf isHandle : Bool) (values : List Nat) :
    stackAsmName conf (copyRetNative perf isHandle (0,0,()) values p) ↔ stackAsmName conf p := by
  exact WordToStackProofs.AsmNameHelpers.copyRetStackAsmName conf perf isHandle (0,0,()) values p

end Flapjack.Test.WordToStackAsmNameHelpersParity

import Flapjack.Compiler.Backend.StackRemove.StackFree
import Flapjack.Compiler.Backend.StackToLab.ExecutedInput

/-! Kernel replays of fresh original native stack_free constructors, including
chunk boundaries, exact Seq association and wrapped word offsets. This is
Flapjack regression infrastructure, not an extra HOL theorem port. -/
namespace Flapjack.Test.StackRemoveStackFree
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

-- free_64_0
example : stackFree (width := 64) 24 0 = (.skip : HolProg 64) := stackFree_zero 24

-- free_64_1
example : stackFree (width := 64) 24 1 = (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8)))) : HolProg 64) := by simp [stackFree, maxStackAlloc, singleStackFree, wordOffset]

-- free_64_255
example : stackFree (width := 64) 24 255 = (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040)))) : HolProg 64) := by simp [stackFree, maxStackAlloc, singleStackFree, wordOffset]

-- free_64_256
example : stackFree (width := 64) 24 256 = (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8))))) : HolProg 64) := by simp [stackFree, maxStackAlloc, singleStackFree, wordOffset]

-- free_64_510
example : stackFree (width := 64) 24 510 = (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) : HolProg 64) := by simp [stackFree, maxStackAlloc, singleStackFree, wordOffset]

-- free_64_511
theorem free64_511 : stackFree (width := 64) 24 511 = (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8)))))) : HolProg 64) := by simp [stackFree, maxStackAlloc, singleStackFree, wordOffset]

-- free_64_512
example : stackFree (width := 64) 24 512 = (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 16)))))) : HolProg 64) := by simp [stackFree, maxStackAlloc, singleStackFree, wordOffset]

-- free_8_256
example : stackFree (width := 8) 24 256 = (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 8 255))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 8 1))))) : HolProg 8) := by simp [stackFree, maxStackAlloc, singleStackFree, wordOffset]

-- free_1_256
example : stackFree (width := 1) 24 256 = (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 1 0))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 1 0))))) : HolProg 1) := by simp [stackFree, maxStackAlloc, singleStackFree, wordOffset]

-- free_80_511
example : stackFree (width := 80) 24 511 = (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 2550))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 2550))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 10)))))) : HolProg 80) := by simp [stackFree, maxStackAlloc, singleStackFree, wordOffset]

-- single_8_256
example : singleStackFree (width := 8) 1234 256 =
    (.inst (.arith (.binop .add 1234 1234 (.imm (BitVec.ofNat 8 0)))) : HolProg 8) := by rfl

-- single_8_511
example : singleStackFree (width := 8) 1234 511 =
    (.inst (.arith (.binop .add 1234 1234 (.imm (BitVec.ofNat 8 255)))) : HolProg 8) := by rfl

-- single_1_255
example : singleStackFree (width := 1) 1234 255 =
    (.inst (.arith (.binop .add 1234 1234 (.imm (BitVec.ofNat 1 0)))) : HolProg 1) := by rfl

-- single_80_511
example : singleStackFree (width := 80) 1234 511 =
    (.inst (.arith (.binop .add 1234 1234 (.imm (BitVec.ofNat 80 5110)))) : HolProg 80) := by rfl

-- The real native-section executed codec accepts the immediate instructions
-- and full large-count Seq; there is no macro expansion or labFlatten fallback.
example : (Flapjack.Compiler.Backend.StackToLab.ExecutedInput.sectionToExecuted?
    (width := 64) (7, stackFree 24 511)).isSome = true := by
  rw [free64_511]
  decide +kernel

-- Skip at zero is distinct from a single zero-immediate instruction.
example : singleStackFree (width := 64) 24 0 ≠ stackFree 24 0 := by
  rw [stackFree_zero]
  intro h
  cases h

#print axioms stackFree_large
end Flapjack.Test.StackRemoveStackFree

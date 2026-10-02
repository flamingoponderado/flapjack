import Flapjack.Compiler.Backend.StackRemove.StackAlloc

/-! Kernel replay of original native allocation constructors, including both check modes. -/

namespace Flapjack.Test.StackRemoveStackAlloc

open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

-- alloc_64_0_0
example : stackAlloc (width := 64) false 24 0 = (.skip : HolProg 64) := by
  simp [stackAlloc]

-- alloc_64_1_0
example : stackAlloc (width := 64) true 24 0 = (.skip : HolProg 64) := by
  simp [stackAlloc]

-- alloc_64_0_1
example : stackAlloc (width := 64) false 24 1 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab, haltInst]

-- alloc_64_1_1
example : stackAlloc (width := 64) true 24 1 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))) (.jumpLower 24 25 2)) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab]

-- alloc_64_0_255
example : stackAlloc (width := 64) false 24 255 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab, haltInst]

-- alloc_64_1_255
example : stackAlloc (width := 64) true 24 255 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.jumpLower 24 25 2)) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab]

-- alloc_64_0_256
example : stackAlloc (width := 64) false 24 256 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip))) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab, haltInst]

-- alloc_64_1_256
example : stackAlloc (width := 64) true 24 256 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.jumpLower 24 25 2)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))) (.jumpLower 24 25 2))) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab]

-- alloc_64_0_510
example : stackAlloc (width := 64) false 24 510 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip))) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab, haltInst]

-- alloc_64_1_510
example : stackAlloc (width := 64) true 24 510 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.jumpLower 24 25 2)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.jumpLower 24 25 2))) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab]

-- alloc_64_0_511
example : stackAlloc (width := 64) false 24 511 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)) (.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)))) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab, haltInst]

-- alloc_64_1_511
example : stackAlloc (width := 64) true 24 511 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.jumpLower 24 25 2)) (.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.jumpLower 24 25 2)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))) (.jumpLower 24 25 2)))) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab]

-- alloc_64_0_512
example : stackAlloc (width := 64) false 24 512 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)) (.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 16))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)))) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab, haltInst]

-- alloc_64_1_512
example : stackAlloc (width := 64) true 24 512 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.jumpLower 24 25 2)) (.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.jumpLower 24 25 2)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 16))))) (.jumpLower 24 25 2)))) : HolProg 64) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab]

-- alloc_8_0_256
example : stackAlloc (width := 8) false 24 256 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 8 255))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 8 2))) (.halt 1)) .skip)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 8 1))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 8 2))) (.halt 1)) .skip))) : HolProg 8) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab, haltInst]

-- alloc_8_1_256
example : stackAlloc (width := 8) true 24 256 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 8 255))))) (.jumpLower 24 25 2)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 8 1))))) (.jumpLower 24 25 2))) : HolProg 8) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab]

-- alloc_1_0_256
example : stackAlloc (width := 1) false 24 256 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 1 0))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 1 0))) (.halt 1)) .skip)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 1 0))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 1 0))) (.halt 1)) .skip))) : HolProg 1) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab, haltInst]

-- alloc_1_1_256
example : stackAlloc (width := 1) true 24 256 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 1 0))))) (.jumpLower 24 25 2)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 1 0))))) (.jumpLower 24 25 2))) : HolProg 1) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab]

-- alloc_80_0_511
example : stackAlloc (width := 80) false 24 511 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 2550))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 80 2))) (.halt 1)) .skip)) (.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 2550))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 80 2))) (.halt 1)) .skip)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 10))))) (.ite .lower 24 (.reg 25) (.seq (.inst (.const 1 (BitVec.ofNat 80 2))) (.halt 1)) .skip)))) : HolProg 80) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab, haltInst]

-- alloc_80_1_511
example : stackAlloc (width := 80) true 24 511 = ((.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 2550))))) (.jumpLower 24 25 2)) (.seq (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 2550))))) (.jumpLower 24 25 2)) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 10))))) (.jumpLower 24 25 2)))) : HolProg 80) := by
  simp [stackAlloc, maxStackAlloc, singleStackAlloc, wordOffset, stackErrLab]

-- single_64_0_0
example : singleStackAlloc (width := 64) false 1234 0 = ((.seq (.inst (.arith (.binop .sub 1234 1234 (.imm (BitVec.ofNat 64 0))))) (.ite .lower 1234 (.reg 1235) (.seq (.inst (.const 1 (BitVec.ofNat 64 2))) (.halt 1)) .skip)) : HolProg 64) := by rfl

-- single_64_1_0
example : singleStackAlloc (width := 64) true 1234 0 = ((.seq (.inst (.arith (.binop .sub 1234 1234 (.imm (BitVec.ofNat 64 0))))) (.jumpLower 1234 1235 2)) : HolProg 64) := by rfl

-- single_8_0_511
example : singleStackAlloc (width := 8) false 1234 511 = ((.seq (.inst (.arith (.binop .sub 1234 1234 (.imm (BitVec.ofNat 8 255))))) (.ite .lower 1234 (.reg 1235) (.seq (.inst (.const 1 (BitVec.ofNat 8 2))) (.halt 1)) .skip)) : HolProg 8) := by rfl

-- single_8_1_511
example : singleStackAlloc (width := 8) true 1234 511 = ((.seq (.inst (.arith (.binop .sub 1234 1234 (.imm (BitVec.ofNat 8 255))))) (.jumpLower 1234 1235 2)) : HolProg 8) := by rfl

-- single_1_0_255
example : singleStackAlloc (width := 1) false 1234 255 = ((.seq (.inst (.arith (.binop .sub 1234 1234 (.imm (BitVec.ofNat 1 0))))) (.ite .lower 1234 (.reg 1235) (.seq (.inst (.const 1 (BitVec.ofNat 1 0))) (.halt 1)) .skip)) : HolProg 1) := by rfl

-- single_1_1_255
example : singleStackAlloc (width := 1) true 1234 255 = ((.seq (.inst (.arith (.binop .sub 1234 1234 (.imm (BitVec.ofNat 1 0))))) (.jumpLower 1234 1235 2)) : HolProg 1) := by rfl

-- single_80_0_511
example : singleStackAlloc (width := 80) false 1234 511 = ((.seq (.inst (.arith (.binop .sub 1234 1234 (.imm (BitVec.ofNat 80 5110))))) (.ite .lower 1234 (.reg 1235) (.seq (.inst (.const 1 (BitVec.ofNat 80 2))) (.halt 1)) .skip)) : HolProg 80) := by rfl

-- single_80_1_511
example : singleStackAlloc (width := 80) true 1234 511 = ((.seq (.inst (.arith (.binop .sub 1234 1234 (.imm (BitVec.ofNat 80 5110))))) (.jumpLower 1234 1235 2)) : HolProg 80) := by rfl

#print axioms stackAlloc_large

end Flapjack.Test.StackRemoveStackAlloc

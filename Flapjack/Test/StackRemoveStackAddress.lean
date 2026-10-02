import Flapjack.Compiler.Backend.StackRemove.StackAddress



/-! Kernel fixtures for original native address-builder outputs; no additional HOL port. -/

namespace Flapjack.Test.StackRemoveStackAddress

open Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang

-- upshift_64_0
example : upshift (width := 64) 24 0 = ((.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 0))))) : HolProg 64) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_64_0
example : downshift (width := 64) 24 0 = ((.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 0))))) : HolProg 64) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_64_0
example : stackStore (width := 64) 24 1234 0 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 0))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 0))))))) : HolProg 64) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_64_0
example : stackLoad (width := 64) 24 0 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 0))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 64) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

-- upshift_64_1
example : upshift (width := 64) 24 1 = ((.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8))))) : HolProg 64) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_64_1
example : downshift (width := 64) 24 1 = ((.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))) : HolProg 64) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_64_1
example : stackStore (width := 64) 24 1234 1 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))))) : HolProg 64) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_64_1
example : stackLoad (width := 64) 24 1 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 64) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

-- upshift_64_255
example : upshift (width := 64) 24 255 = ((.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) : HolProg 64) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_64_255
example : downshift (width := 64) 24 255 = ((.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) : HolProg 64) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_64_255
example : stackStore (width := 64) 24 1234 255 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))))) : HolProg 64) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_64_255
example : stackLoad (width := 64) 24 255 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 64) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

-- upshift_64_256
example : upshift (width := 64) 24 256 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8)))))) : HolProg 64) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_64_256
example : downshift (width := 64) 24 256 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8)))))) : HolProg 64) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_64_256
example : stackStore (width := 64) 24 1234 256 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8)))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8)))))))) : HolProg 64) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_64_256
example : stackLoad (width := 64) 24 256 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8)))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 64) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

-- upshift_64_510
example : upshift (width := 64) 24 510 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040)))))) : HolProg 64) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_64_510
example : downshift (width := 64) 24 510 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040)))))) : HolProg 64) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_64_510
example : stackStore (width := 64) 24 1234 510 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040)))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040)))))))) : HolProg 64) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_64_510
example : stackLoad (width := 64) 24 510 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040)))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 64) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

-- upshift_64_511
example : upshift (width := 64) 24 511 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8))))))) : HolProg 64) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_64_511
example : downshift (width := 64) 24 511 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))))) : HolProg 64) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_64_511
example : stackStore (width := 64) 24 1234 511 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8))))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 8))))))))) : HolProg 64) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_64_511
example : stackLoad (width := 64) 24 511 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 8))))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 64) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

-- upshift_64_512
example : upshift (width := 64) 24 512 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 16))))))) : HolProg 64) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_64_512
example : downshift (width := 64) 24 512 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 16))))))) : HolProg 64) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_64_512
example : stackStore (width := 64) 24 1234 512 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 16))))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 64 16))))))))) : HolProg 64) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_64_512
example : stackLoad (width := 64) 24 512 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 2040))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 64 16))))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 64) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

-- upshift_8_256
example : upshift (width := 8) 24 256 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 8 255))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 8 1)))))) : HolProg 8) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_8_256
example : downshift (width := 8) 24 256 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 8 255))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 8 1)))))) : HolProg 8) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_8_256
example : stackStore (width := 8) 24 1234 256 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 8 255))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 8 1)))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 8 255))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 8 1)))))))) : HolProg 8) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_8_256
example : stackLoad (width := 8) 24 256 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 8 255))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 8 1)))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 8) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

-- upshift_1_256
example : upshift (width := 1) 24 256 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 1 0))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 1 0)))))) : HolProg 1) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_1_256
example : downshift (width := 1) 24 256 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 1 0))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 1 0)))))) : HolProg 1) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_1_256
example : stackStore (width := 1) 24 1234 256 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 1 0))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 1 0)))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 1 0))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 1 0)))))))) : HolProg 1) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_1_256
example : stackLoad (width := 1) 24 256 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 1 0))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 1 0)))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 1) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

-- upshift_80_511
example : upshift (width := 80) 24 511 = ((.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 2550))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 2550))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 10))))))) : HolProg 80) := by
  simp [upshift, maxStackAlloc, wordOffset]

-- downshift_80_511
example : downshift (width := 80) 24 511 = ((.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 2550))))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 2550))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 10))))))) : HolProg 80) := by
  simp [downshift, maxStackAlloc, wordOffset]

-- stack_store_80_511
example : stackStore (width := 80) 24 1234 511 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 2550))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 2550))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 10))))))) (.seq (.inst (.mem .store 1234 (.addr 24 0))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 2550))))) (.seq (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 2550))))) (.inst (.arith (.binop .sub 24 24 (.imm (BitVec.ofNat 80 10))))))))) : HolProg 80) := by
  simp [stackStore, upshift, downshift, maxStackAlloc, wordOffset]

-- stack_load_80_511
example : stackLoad (width := 80) 24 511 = ((.seq (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 2550))))) (.seq (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 2550))))) (.inst (.arith (.binop .add 24 24 (.imm (BitVec.ofNat 80 10))))))) (.inst (.mem .load 24 (.addr 24 0)))) : HolProg 80) := by
  simp [stackLoad, upshift, maxStackAlloc, wordOffset]

#print axioms upshift_large

#print axioms downshift_large

end Flapjack.Test.StackRemoveStackAddress

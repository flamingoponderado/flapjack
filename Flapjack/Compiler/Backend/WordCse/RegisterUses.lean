import Flapjack.Compiler.Backend.WordCse.InstructionKeys

/-! Native CSE register classifiers. Carry reads its flag register; overflow
operations omit their output flag from reads. Production replacement remains
on the CSE definition frontier. -/
namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm

-- riscv-mi: declaration over the reduced integer carrier.
def firstRegOfArith {width : Nat} [NeZero width] : HolArith width → Nat
  | .binop _ r _ _ | .shift _ r _ _ | .div r _ _
  | .longMul r _ _ _ | .longDiv r _ _ _ _
  | .addCarry r _ _ _ | .addOverflow r _ _ _ | .subOverflow r _ _ _ => r

-- riscv-mi: declaration over the reduced integer carrier.
def arithWrites {width : Nat} [NeZero width] : HolArith width → List Nat
  | .binop _ r _ _ | .shift _ r _ _ | .div r _ _ => [r]
  | .longMul r1 r2 _ _ | .longDiv r1 r2 _ _ _ => [r1, r2]
  | .addCarry r1 _ _ r4 | .addOverflow r1 _ _ r4 | .subOverflow r1 _ _ r4 => [r1, r4]

-- riscv-mi: declaration over the reduced integer carrier.
def arithReads {width : Nat} [NeZero width] : HolArith width → List Nat
  | .binop _ _ r2 (.reg r3) | .shift _ _ r2 (.reg r3) => [r2, r3]
  | .binop _ _ r2 (.imm _) | .shift _ _ r2 (.imm _) => [r2]
  | .div _ r2 r3 | .longMul _ _ r2 r3 => [r2, r3]
  | .longDiv _ _ r3 r4 r5 => [r3, r4, r5]
  | .addCarry _ r2 r3 r4 => [r2, r3, r4]
  | .addOverflow _ r2 r3 _ | .subOverflow _ r2 r3 _ => [r2, r3]


-- riscv-mi: declaration over the reduced integer carrier.
def canMemArith {width : Nat} [NeZero width] : HolArith width → Bool
  | .binop _ _ r1 (.reg r2) | .div _ r1 r2 => r1 % 2 == 1 && r2 % 2 == 1
  | .binop _ _ r1 (.imm _) | .shift _ _ r1 (.imm _) => r1 % 2 == 1
  | _ => false

@[hol "cakeml/compiler/backend/word_cseScript.sml" "is_store_def"]
def isStore : HolMemop → Bool
  | .load | .load8 | .load16 | .load32 => false
  | .store | .store8 | .store16 | .store32 => true

end Flapjack.Compiler.Backend.WordCse

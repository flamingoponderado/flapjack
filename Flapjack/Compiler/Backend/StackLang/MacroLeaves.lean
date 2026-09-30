import Flapjack.RiscV.Lab

/-!
# Production macro leaf projection

Flapjack-only infrastructure, not a HOL port: `StackProg.const`, `.arith`,
and `.shift` are production conveniences with no corresponding StackLang
constructor. Project them to the existing literal WordInst subset that the
canonical program codec accepts. The constant's Nat word-width bound is
explicit; WordPayloads.Bounded does not cover this Nat-only macro field.

The equations compare actual RISC-V instruction-list emission and stored
Lab line length for an isolated leaf, including invalid-register errors and
ROR scratch restrictions. They do not establish complete labFlatten or
StackLang transition equivalence. In particular, the Seq const/arith/memory
peepholes in labFlatten must be addressed before transforming a whole program
or replacing the executed StackNames route. No performance exception is claimed.
-/
namespace Flapjack.Compiler.Backend.StackLang.MacroLeaves
open Flapjack Flapjack.RiscV

/-- Partial projection of precisely the three production-only macro leaves.
Every other constructor is rejected; this is not a whole-program compiler. -/
def project (width : Nat) : StackProg Nat → Option (StackProg (BitVec width))
  | .const destination value =>
      if value < 2 ^ width then some (.inst (.const destination (BitVec.ofNat width value)))
      else none
  | .arith operator destination left right =>
      some (.inst (.arith (.binOp operator destination left (.reg right))))
  | .shift operator destination left right =>
      some (.inst (.arith (.shift operator destination left (.reg right))))
  | _ => none

/-- Numeric bound on the macro's own Nat field, independently of the shared
word-payload invariant, retains the exact constant supplied to the assembler. -/
theorem const_emission {width : Nat} [NeZero width] (destination value : Nat)
    (hvalue : value < 2 ^ width) :
    labCompilePlain (width := width) (.const destination value) =
      labCompilePlain (.word (.const destination (BitVec.ofNat width value))) := by
  cases hd : registerOfNat destination <;>
    by_cases hv : value < 2 ^ 11 <;>
    simp [labCompilePlain, labRegisterOfNat_portToStack_all,
      portZeroRegister, registerOfNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hvalue, labConstInstructions, hv]

/-- All register conversion failures are retained, without a success premise. -/
theorem arith_emission {width : Nat} [NeZero width]
    (operator : BinOp) (destination left right : Nat) :
    labCompilePlain (width := width) (.arith operator destination left right) =
      labCompilePlain (.word (.arith (.binOp operator destination left (.reg right)))) := by
  cases hd : registerOfNat destination <;>
    cases hl : registerOfNat left <;>
    cases hr : registerOfNat right <;> cases operator <;>
    simp [labCompilePlain, labBinOpInstruction, wordArithToInstructions,
      wordArithToInstruction, labRegisterOfNat_portToStack_all, hd, hl, hr] <;> rfl

/-- Variable ROR retains the reserved-register rejection and all five emitted
instructions; ordinary shifts retain both register errors and instructions. -/
theorem shift_emission {width : Nat} [NeZero width]
    (operator : Shift) (destination left right : Nat) :
    labCompilePlain (width := width) (.shift operator destination left right) =
      labCompilePlain (.word (.arith (.shift operator destination left (.reg right)))) := by
  cases hd : registerOfNat destination <;>
    cases hl : registerOfNat left <;>
    cases hr : registerOfNat right <;> cases operator <;>
    simp [labCompilePlain, labShiftInstructions, wordArithToInstructions,
      wordArithToInstruction, labRegisterOfNat_portToStack_all,
      portZeroRegister, Bool.or_assoc, hd, hl, hr]

/-- Exact leaf lengths, needed before replacing any label-positioning input. -/
theorem const_length {width : Nat} [NeZero width] (destination value : Nat)
    (hvalue : value < 2 ^ width) :
    labLineInstructionCount (width := width) (.asm (.const destination value) [] 0) =
      labLineInstructionCount (width := width)
        (.asm (.word (.const destination (BitVec.ofNat width value))) [] 0) := by
  simp [labLineInstructionCount, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hvalue]

theorem arith_length {width : Nat} (operator : BinOp) (destination left right : Nat) :
    labLineInstructionCount (width := width) (.asm (.arith operator destination left right) [] 0) =
      labLineInstructionCount (width := width)
        (.asm (.word (.arith (.binOp operator destination left (.reg right)))) [] 0) := by
  cases operator <;> rfl

theorem shift_length {width : Nat} (operator : Shift) (destination left right : Nat) :
    labLineInstructionCount (width := width) (.asm (.shift operator destination left right) [] 0) =
      labLineInstructionCount (width := width)
        (.asm (.word (.arith (.shift operator destination left (.reg right)))) [] 0) := by
  cases operator <;> rfl

end Flapjack.Compiler.Backend.StackLang.MacroLeaves

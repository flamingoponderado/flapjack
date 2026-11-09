module

public import Flapjack.Compiler.Backend.LabToTarget.Encoding
public import Flapjack.Compiler.Encoders.RiscV.Unsupported

@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Encoding guard before native encoding

`lab_to_target$line_ok_light` accepts every `Asm` line, and the RISC-V encoder
narrows each register with `BitVec.ofNat 5 r` (`riscv_ast_def`), so a register
outside the target's register file would silently become a different register
instead of being rejected.  `riscvAst` also maps `Arith (LongDiv ...)` and
`FP _` to `riscv_encode_fail_def`, silently substituting the fail encoding
(`Skip` is the padding instruction and its fail encoding is the intended
no-op, so it is accepted).  `riscv_enc_def`/`riscv_ast_def` stay exact; this
module is Flapjack-only driver infrastructure that checks the
`Asm` lines of the `stack_to_lab` output before encoding and reports the first
line that cannot be encoded, with a named reason:

- a register that `asm$reg_ok` rejects (`reg < reg_count` and not in
  `avoid_regs`);
- an instruction shape the target encoder rejects.

`LabAsm` lines are not inspected here: their registers are chosen by
`stack_to_lab` from the same target configuration (through
`StackNames.compileHOL`), and `lab_inst_def` only produces `Jump`, `JumpCmp`,
`Call` and `Loc`, none of which is a fail shape.  The guard is a no-op on
every program the pass actually supports.  There is no separately named HOL
declaration for this guard.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV
open Flapjack.Basis.Pure.MlString

/-- A lab line over the exact assembler carriers, as `stack_to_lab` produces
it for `lab_to_target`. -/
abbrev GuardLine (width : Nat) [NeZero width] :=
  Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)

/-- A lab section over the exact assembler carriers. -/
abbrev GuardSection (width : Nat) [NeZero width] := Section (GuardLine width)

/-- A located reason an `Asm` line cannot be encoded for this target.
`sectionIndex` and `lineIndex` are zero-based positions in the lab program. -/
inductive EncodingGuardFailure where
  | outOfRange (sectionIndex lineIndex register : Nat)
  | avoided (sectionIndex lineIndex register : Nat)
  | unsupported (sectionIndex lineIndex : Nat) (reason : UnsupportedReason)
  deriving DecidableEq, Repr

/-- Human-readable description of a located encoding failure. -/
def encodingGuardFailureDescription : EncodingGuardFailure → String
  | .outOfRange sectionIndex lineIndex register =>
      "lab-to-target: section " ++ toString sectionIndex ++ " line " ++
        toString lineIndex ++ " uses register " ++ toString register ++
        ", which is outside the target's register count"
  | .avoided sectionIndex lineIndex register =>
      "lab-to-target: section " ++ toString sectionIndex ++ " line " ++
        toString lineIndex ++ " uses register " ++ toString register ++
        ", which the target reserves"
  | .unsupported sectionIndex lineIndex reason =>
      "lab-to-target: section " ++ toString sectionIndex ++ " line " ++
        toString lineIndex ++ " cannot be encoded: " ++
        unsupportedReasonDescription reason

/-- Every register of an exact `arith` payload. -/
def arithRegisters {width : Nat} [NeZero width] : HolArith width → List Nat
  | .binop _ destination source (.reg right) => [destination, source, right]
  | .binop _ destination source (.imm _) => [destination, source]
  | .shift _ destination source (.reg right) => [destination, source, right]
  | .shift _ destination source (.imm _) => [destination, source]
  | .div destination dividend divisor => [destination, dividend, divisor]
  | .longMul destinationLeft destinationRight sourceLeft sourceRight =>
      [destinationLeft, destinationRight, sourceLeft, sourceRight]
  | .longDiv destinationLeft destinationRight sourceLeft sourceRight quotient =>
      [destinationLeft, destinationRight, sourceLeft, sourceRight, quotient]
  | .addCarry destination resultCarry sourceLeft sourceRight =>
      [destination, resultCarry, sourceLeft, sourceRight]
  | .addOverflow destination resultCarry sourceLeft sourceRight =>
      [destination, resultCarry, sourceLeft, sourceRight]
  | .subOverflow destination resultCarry sourceLeft sourceRight =>
      [destination, resultCarry, sourceLeft, sourceRight]

/-- Every integer register of an exact instruction.  FP payloads are excluded:
this target does not lower them (`riscvAst` emits the fail encoding), so no
FP register is narrowed by the encoder. -/
def instRegisters {width : Nat} [NeZero width] : HolInst width → List Nat
  | .skip => []
  | .const destination _ => [destination]
  | .arith operation => arithRegisters operation
  | .mem _ destination (.addr base _) => [destination, base]
  | .fp _ => []

/-- Every integer register of an exact assembler instruction. -/
def asmRegisters {width : Nat} [NeZero width] : HolAsm width → List Nat
  | .inst instruction => instRegisters instruction
  | .jump _ => []
  | .jumpCmp _ source (.reg right) _ => [source, right]
  | .jumpCmp _ source (.imm _) _ => [source]
  | .call _ => []
  | .jumpReg target => [target]
  | .loc register _ => [register]

/-- Classify a register that `asm$reg_ok` rejects: outside the register count,
or in the target's avoid set. -/
def classifyRegister {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (sectionIndex lineIndex register : Nat) : EncodingGuardFailure :=
  if register < config.regCount then .avoided sectionIndex lineIndex register
  else .outOfRange sectionIndex lineIndex register

/-- The first register in the list that `asm$reg_ok` rejects, if any. -/
private def firstFailureInList {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (sectionIndex lineIndex : Nat) :
    List Nat → Option EncodingGuardFailure
  | [] => none
  | register :: rest =>
      if asmRegOkExact register config then
        firstFailureInList config sectionIndex lineIndex rest
      else some (classifyRegister config sectionIndex lineIndex register)

/-- The first reason one lab line cannot be encoded: a rejected register, then
an unsupported instruction shape.  `LabAsm` and `Label` lines carry no checked
register and no fail shape. -/
private def firstFailureInLine {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (unsupported : HolAsm width → Option UnsupportedReason)
    (sectionIndex lineIndex : Nat) (line : GuardLine width) :
    Option EncodingGuardFailure :=
  match line with
  | .asm instruction _ _ =>
      let asm := cbwToAsmExact instruction
      match firstFailureInList config sectionIndex lineIndex (asmRegisters asm) with
      | some failure => some failure
      | none =>
          match unsupported asm with
          | some reason => some (.unsupported sectionIndex lineIndex reason)
          | none => none
  | _ => none

/-- The first encoding failure of a section's lines, in line order. -/
private def firstFailureInLines {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (unsupported : HolAsm width → Option UnsupportedReason)
    (sectionIndex lineIndex : Nat) : List (GuardLine width) →
      Option EncodingGuardFailure
  | [] => none
  | line :: rest =>
      match firstFailureInLine config unsupported sectionIndex lineIndex line with
      | some failure => some failure
      | none => firstFailureInLines config unsupported sectionIndex (lineIndex + 1) rest

/-- The first encoding failure across sections, in section and line order. -/
private def firstFailureInSections {width : Nat} [NeZero width]
    (config : AsmConfigExact width)
    (unsupported : HolAsm width → Option UnsupportedReason)
    (sectionIndex : Nat) : List (GuardSection width) → Option EncodingGuardFailure
  | [] => none
  | ⟨_, lines⟩ :: rest =>
      match firstFailureInLines config unsupported sectionIndex 0 lines with
      | some failure => some failure
      | none => firstFailureInSections config unsupported (sectionIndex + 1) rest

/-- The encoding guard: `none` exactly when every `Asm` line of the lab program
satisfies `asm$reg_ok` for this target configuration and has a defined
lowering under the supplied unsupported-shape check. -/
def firstUnencodable {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (unsupported : HolAsm width → Option UnsupportedReason)
    (sections : List (GuardSection width)) : Option EncodingGuardFailure :=
  firstFailureInSections config unsupported 0 sections

end Flapjack.Compiler.Backend.LabToTarget

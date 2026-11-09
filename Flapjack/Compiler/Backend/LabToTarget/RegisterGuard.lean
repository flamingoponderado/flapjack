import Flapjack.Compiler.Backend.LabToTarget.Encoding

/-!
# Register-range guard before native encoding

`lab_to_target$line_ok_light` accepts every `Asm` line, and the RISC-V
encoder narrows each register with `BitVec.ofNat 5 r` (`riscv_ast_def`), so a
register outside the target's register file would silently become a different
register instead of being rejected.  `riscv_enc_def`/`riscv_ast_def` stay
exact; this module is Flapjack-only driver infrastructure that checks the
`Asm` lines of the `stack_to_lab` output before encoding and reports the first
register that `asm$reg_ok` rejects (`reg < reg_count` and not in
`avoid_regs`).

`LabAsm` lines are not inspected here: their registers are chosen by
`stack_to_lab` from the same target configuration (through
`StackNames.compileHOL`), not carried over from a source program.  The guard
is a no-op on every program the pass actually supports.  There is no
separately named HOL declaration for this guard.
-/

namespace Flapjack.Compiler.Backend.LabToTarget

open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString

/-- A lab line over the exact assembler carriers, as `stack_to_lab` produces
it for `lab_to_target`. -/
abbrev GuardLine (width : Nat) [NeZero width] :=
  Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
    (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width)

/-- A lab section over the exact assembler carriers. -/
abbrev GuardSection (width : Nat) [NeZero width] := Section (GuardLine width)

/-- A located register-range failure.  `sectionIndex` and `lineIndex` are
zero-based positions in the lab program. -/
inductive RegisterGuardFailure where
  | outOfRange (sectionIndex lineIndex register : Nat)
  | avoided (sectionIndex lineIndex register : Nat)
  deriving DecidableEq, Repr

/-- Human-readable description of a located register-range failure. -/
def registerGuardFailureDescription : RegisterGuardFailure → String
  | .outOfRange sectionIndex lineIndex register =>
      "lab-to-target: section " ++ toString sectionIndex ++ " line " ++
        toString lineIndex ++ " uses register " ++ toString register ++
        ", which is outside the target's register count"
  | .avoided sectionIndex lineIndex register =>
      "lab-to-target: section " ++ toString sectionIndex ++ " line " ++
        toString lineIndex ++ " uses register " ++ toString register ++
        ", which the target reserves"

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
    (sectionIndex lineIndex register : Nat) : RegisterGuardFailure :=
  if register < config.regCount then .avoided sectionIndex lineIndex register
  else .outOfRange sectionIndex lineIndex register

/-- The first register in the list that `asm$reg_ok` rejects, if any. -/
private def firstBadRegisterInList {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (sectionIndex lineIndex : Nat) :
    List Nat → Option RegisterGuardFailure
  | [] => none
  | register :: rest =>
      if asmRegOkExact register config then
        firstBadRegisterInList config sectionIndex lineIndex rest
      else some (classifyRegister config sectionIndex lineIndex register)

/-- The first rejected register of one lab line; `LabAsm` and `Label` lines
carry no checked register. -/
private def firstBadRegisterInLine {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (sectionIndex lineIndex : Nat)
    (line : GuardLine width) : Option RegisterGuardFailure :=
  match line with
  | .asm instruction _ _ =>
      firstBadRegisterInList config sectionIndex lineIndex
        (asmRegisters (cbwToAsmExact instruction))
  | _ => none

/-- The first rejected register of a section's lines, in line order. -/
private def firstBadRegisterInLines {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (sectionIndex lineIndex : Nat) :
    List (GuardLine width) → Option RegisterGuardFailure
  | [] => none
  | line :: rest =>
      match firstBadRegisterInLine config sectionIndex lineIndex line with
      | some failure => some failure
      | none => firstBadRegisterInLines config sectionIndex (lineIndex + 1) rest

/-- The first rejected register across sections, in section and line order. -/
private def firstBadRegisterInSections {width : Nat} [NeZero width]
    (config : AsmConfigExact width) (sectionIndex : Nat) :
    List (GuardSection width) → Option RegisterGuardFailure
  | [] => none
  | ⟨_, lines⟩ :: rest =>
      match firstBadRegisterInLines config sectionIndex 0 lines with
      | some failure => some failure
      | none => firstBadRegisterInSections config (sectionIndex + 1) rest

/-- The register-range guard: `none` exactly when every `Asm` line of the lab
program satisfies `asm$reg_ok` for this target configuration. -/
def firstBadRegister {width : Nat} [NeZero width] (config : AsmConfigExact width)
    (sections : List (GuardSection width)) : Option RegisterGuardFailure :=
  firstBadRegisterInSections config 0 sections

end Flapjack.Compiler.Backend.LabToTarget

import Flapjack.Compiler.Backend.WordToStack.Proofs.AsmNameShare

namespace Flapjack.WordToStackProofs.AsmNameInstructions
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStackRegFormat
open Flapjack.WordToStackProofs.AsmNameShare

/- Flapjack-only equation interfaces for the generated frame-store wrappers.
There is no separately named HOL theorem for these case-proof calculations. -/
theorem writeNameEquation {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (body : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat) :
    stackAsmName conf (wRegWrite1Native body r frame) ↔
      stackAsmName conf (body (if r / 2 < frame.1 then r / 2 else frame.1)) := by
  simp only [wRegWrite1Native]
  split <;> simp only [stackAsmName, and_true]

theorem write2NameEquation {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (body : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat) :
    stackAsmName conf (wRegWrite2Native body r frame) ↔
      stackAsmName conf (body (if r / 2 < frame.1 then r / 2 else frame.1 + 1)) := by
  simp only [wRegWrite2Native]
  split <;> simp only [stackAsmName, and_true]

/-- Logical register names for both generated read temporaries. These bounds
are Flapjack infrastructure used inside the HOL compiler case, not an extra
public compiler premise or a port of a separately named HOL declaration. -/
theorem readNames {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (r : Nat) (frame : Nat × Nat × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length) :
    regName (wReg1 r frame).2 conf ∧ regName (wReg2 r frame).2 conf := by
  simp only [wReg1, wReg2, regName]
  split <;> omega

/-- Internal memory-instruction calculation. The ordinary 16-bit source forms
use the original wInst fallback; the other six preserve their checked offsets.
There is no separately named HOL theorem for this case-proof calculation. -/
theorem memoryName {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (op : HolMemop) (destination base : Nat) (offset : BitVec width)
    (frame : Nat × Nat × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (valid : instOkLessExact conf (.mem op destination (.addr base offset)) = true) :
    stackAsmName conf (wInstNative (.mem op destination (.addr base offset)) frame) := by
  cases op
  all_goals simp only [wInstNative, loadName, writeNameEquation, wReg1, wReg2]
  all_goals try split_ifs
  all_goals simp_all [stackAsmName, instName, addrName, regName, instOkLessExact]
  all_goals omega

/-- Internal arithmetic case calculation with precisely the source validity,
physical-register, argument-placement and conditional two-register facts.
These are extracted from the original compiler guards, not new public premises. -/
theorem arithmeticName {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (instruction : WordLangArith (BitVec width)) (frame : Nat × Nat × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (minimum : 4 < frame.1)
    (physical : everyVarInstHOL isPhyVar (.arith instruction) = true)
    (convention : instArgConvention (.arith instruction) = true)
    (valid : instOkLessExact conf (.arith (HolArith.ofWordLangArith instruction)) = true)
    (twoReg : conf.twoRegArith = true →
      twoRegInstExact (.arith (HolArith.ofWordLangArith instruction)) = true) :
    stackAsmName conf
      (wInstNative (.arith (HolArith.ofWordLangArith instruction)) frame) := by
  cases instruction
  case' binop _ _ _ operand => cases operand
  case' shift _ _ _ operand => cases operand
  all_goals simp only [everyVarInstHOL, everyVarImmHOL, isPhyVar,
    Bool.and_eq_true, decide_eq_true_eq] at physical
  all_goals simp only [HolArith.ofWordLangArith, HolRegImm.ofWordRegImm] at *
  all_goals simp only [wInstNative, loadName, writeNameEquation, wReg1, wReg2]
  all_goals try split_ifs
  all_goals simp_all [stackAsmName, instName, arithName, regName, regImmName,
    instArgConvention, instOkLessExact, twoRegInstExact]
  all_goals repeat' first | apply And.intro | intro
  all_goals try simp_all
  all_goals try omega
  all_goals first
    | simpa only [or_assoc] using valid
    | (rcases valid with valid | valid
       all_goals try simp_all
       all_goals omega)

/-- Entire original Inst case of the naming theorem, with all seven original
guards retained and the actual compiler output. All arithmetic, memory and FP
forms are discharged internally, including the original ordinary-16-bit fallback,
two-register restrictions and the positive-width 32/64-bit FP move distinctions.
The no-share guard remains although this constructor itself is not shared memory. -/
theorem wordToStackStackAsmNameInst {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (instruction : WordLangInst (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat) (plain : perf = false)
    (conventions : postAllocConventionsHOL frame.1 (.inst instruction) = true)
    (valid : fullInstOkLessExact conf (.inst instruction) = true)
    (twoReg : conf.twoRegArith = true →
      everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i))
        (.inst instruction) = true)
    (_noShare : noShareInstSubprogsHOL (.inst instruction) = true ∨ conf.isa ≠ .ag32)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.inst instruction) bs frame).1 := by
  subst perf
  simp only [compNative]
  simp only [postAllocConventionsHOL, everyVarHOL, Bool.and_eq_true] at conventions
  have physical := conventions.1
  have convention : instArgConvention instruction = true := conventions.2.2
  simp only [fullInstOkLessExact, fullInstOkLessWith] at valid
  simp only [everyInst] at twoReg
  cases instruction with
  | arith operation =>
      simp only [HolInst.ofWordLangInst] at valid twoReg ⊢
      exact arithmeticName conf operation frame room minimum physical convention valid twoReg
  | mem operator destination address =>
      cases address with
      | addr base offset =>
          simp only [HolInst.ofWordLangInst, HolAddr.ofWordLangAddr] at valid ⊢
          exact memoryName conf operator destination base offset frame room valid
  | const destination value =>
      simp only [HolInst.ofWordLangInst, wInstNative, writeNameEquation]
      split <;> simp only [stackAsmName, instName, regName] <;> omega
  | skip => trivial

end Flapjack.WordToStackProofs.AsmNameInstructions

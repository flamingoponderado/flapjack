import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.StackProps.ProgramNames
import Flapjack.Pancake.WordConvs.FullInstOkLess
import Flapjack.Pancake.WordConvs.NotCreated
import Mathlib.Tactic.SplitIfs

namespace Flapjack.WordToStackProofs.AsmNameShare
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Flapjack-only equation for the naming predicate on generated frame loads.
HOL uses this reduction inside the compiler-case proof, with no named original. -/
theorem loadName {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (loads : List (Nat × Nat)) (body : HolProg width) :
    stackAsmName conf (wStackLoadNative loads body) ↔ stackAsmName conf body := by
  induction loads with
  | nil => rfl
  | cons x xs ih => cases x; simpa only [wStackLoadNative, stackAsmName, true_and] using ih

private theorem shareName {width : Nat} [NeZero width] (conf : AsmConfigExact width)
    (op : HolMemop) (v ad : Nat) (offset : BitVec width) (frame : Nat × Nat × Nat)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (notAg32 : conf.isa ≠ .ag32)
    (valid : (if op == .load || op == .store || op == .load32 || op == .store32 then
        asmAddrOffsetOkExact conf offset
      else if op == .load16 || op == .store16 then asmHwOffsetOkExact conf offset
      else asmByteOffsetOkExact conf offset) = true) :
    stackAsmName conf (wShareInstNative op v (.addr ad offset) frame) := by
  cases op
  all_goals simp only [wShareInstNative, loadName, wRegWrite1Native, wReg1, wReg2]
  all_goals try split_ifs
  all_goals simp_all [stackAsmName, addrName, regName]
  all_goals omega

/-- Entire original ShareInst case of the naming theorem. All seven original
guards and the actual compiler output are retained. The source no-share guard
forces a non-Ag32 ISA here; failed address extraction is ruled out by validity.
Physical-register conventions, the two-register guard, and the strict frame
minimum are retained even though this case needs only offset validity and room. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_stack_asm_name_lem" (words_as_type_indexed_bitvec)]
theorem wordToStackStackAsmNameShareInst {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (op : HolMemop) (v : Nat)
    (exp : WordLangExpHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (plain : perf = false)
    (_conventions : postAllocConventionsHOL frame.1 (.shareInst op v exp) = true)
    (valid : fullInstOkLessExact conf (.shareInst op v exp) = true)
    (_twoReg : conf.twoRegArith = true →
      everyInst (fun i => twoRegInstExact (HolInst.ofWordLangInst i))
        (.shareInst op v exp) = true)
    (noShare : noShareInstSubprogsHOL (.shareInst op v exp) = true ∨ conf.isa ≠ .ag32)
    (room : frame.1 + 1 < conf.regCount - conf.avoidRegs.length)
    (_minimum : 4 < frame.1) :
    stackAsmName conf (compNative conf perf (.shareInst op v exp) bs frame).1 := by
  subst perf
  have notAg32 : conf.isa ≠ .ag32 := by
    simpa only [noShareInstSubprogsHOL, notCreatedSubprogsWithMemOp,
      Bool.false_eq_true, false_or] using noShare
  cases extracted : expToAddrHOL exp with
  | none =>
      simp only [fullInstOkLessExact, fullInstOkLessWith, extracted] at valid
      contradiction
  | some address =>
      cases address with
      | addr ad offset =>
          simp only [fullInstOkLessExact, fullInstOkLessWith, extracted] at valid
          simp only [compNative, extracted, HolAddr.ofWordLangAddr]
          exact shareName conf op v ad offset frame room notAg32 valid

end Flapjack.WordToStackProofs.AsmNameShare

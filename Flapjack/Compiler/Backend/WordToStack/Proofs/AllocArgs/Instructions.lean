import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.StackProps.AllocArg

namespace Flapjack.WordToStackProofs.AllocArgs
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-specific intermediate from the source instruction-case proof:
ordered loads preserve the entire continuation predicate. No separate HOL
declaration names this fact. -/
theorem loadAllocArg {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (p : HolProg width) :
    allocArg (wStackLoadNative loads p) ↔ allocArg p := by
  induction loads with
  | nil => rfl
  | cons pair loads ih =>
      rcases pair with ⟨r,i⟩
      simpa [wStackLoadNative, allocArg] using ih

/-- Flapjack-specific callback calculation inside the source instruction case,
not a separately named HOL result. -/
theorem write1AllocArg {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat)
    (h : ∀ reg, allocArg (g reg)) : allocArg (wRegWrite1Native g r frame) := by
  simp only [wRegWrite1Native]
  split <;> simp [allocArg, h]

/-- Flapjack-specific second-register callback calculation used by the original
non-64-bit FP transfer case, with its internal callback premise. -/
theorem write2AllocArg {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (frame : Nat × Nat × Nat)
    (h : ∀ reg, allocArg (g reg)) : allocArg (wRegWrite2Native g r frame) := by
  simp only [wRegWrite2Native]
  split <;> simp [allocArg, h]

/-- Flapjack-specific complete instruction calculation from the original
compiler proof. All constructors, including ordinary 16-bit memory catchalls
and the width-sensitive FP clauses, remain quantified. -/
theorem instAllocArg {width : Nat} [NeZero width]
    (instruction : HolInst width) (frame : Nat × Nat × Nat) :
    allocArg (wInstNative instruction frame) := by
  have write1 (g : Nat → HolInst width) (r : Nat) :
      allocArg (wRegWrite1Native (fun reg => .inst (g reg)) r frame) :=
    write1AllocArg _ r frame (fun _ => trivial)
  have write21 (g : Nat → Nat → HolInst width) (r1 r2 : Nat) :
      allocArg (wRegWrite2Native
        (fun reg2 => wRegWrite1Native (fun reg1 => .inst (g reg1 reg2)) r1 frame)
        r2 frame) :=
    write2AllocArg _ r2 frame (fun reg2 => write1 (fun reg1 => g reg1 reg2) r1)
  cases instruction with
  | arith a =>
      cases a <;> try (rename_i op d s ri; cases ri)
      all_goals simp [wInstNative, loadAllocArg, write1, allocArg]
  | mem op d addr =>
      cases addr
      cases op <;> simp [wInstNative, loadAllocArg, write1, allocArg]
  | fp f =>
      cases f
      all_goals
        by_cases hw : width = 64
        all_goals simp [wInstNative, hw, loadAllocArg, write1, write21, allocArg]
  | skip => trivial
  | const n c => simp [wInstNative, write1]

/-- Flapjack-specific helper calculation inside the original shared-memory
compiler case. Every memory operation and arbitrary offset is retained. -/
theorem shareAllocArg {width : Nat} [NeZero width]
    (op : HolMemop) (v : Nat) (addr : HolAddr width) (frame : Nat × Nat × Nat) :
    allocArg (wShareInstNative op v addr frame) := by
  cases addr
  cases op <;> simp only [wShareInstNative, loadAllocArg]
  all_goals first
    | exact write1AllocArg _ _ _ (fun _ => trivial)
    | trivial

/-- Entire Inst case of the original compiler theorem. Its original performance
equality is the only premise; the actual native compiler result is concluded. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_alloc_arg" (words_as_type_indexed_bitvec)]
theorem wordToStackAllocArgInst {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (instruction : WordLangInst (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) :
    allocArg (compNative conf perf (.inst instruction) bs frame).1 := by
  subst perf
  simp only [compNative]
  exact instAllocArg (HolInst.ofWordLangInst instruction) frame

/-- Entire ShareInst case, including every expression whose address extraction
fails. No successful extraction or instruction restriction is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_alloc_arg" (words_as_type_indexed_bitvec)]
theorem wordToStackAllocArgShareInst {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool) (op : HolMemop) (v : Nat)
    (exp : WordLangExpHOL (BitVec width)) (bs : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (plain : perf = false) :
    allocArg (compNative conf perf (.shareInst op v exp) bs frame).1 := by
  subst perf
  cases h : expToAddrHOL exp <;> simp only [compNative, h]
  · trivial
  · exact shareAllocArg _ _ _ frame

end Flapjack.WordToStackProofs.AllocArgs

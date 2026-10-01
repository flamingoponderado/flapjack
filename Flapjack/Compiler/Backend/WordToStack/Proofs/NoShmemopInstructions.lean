import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopHelpers
import Flapjack.Pancake.WordConvs.NotCreated

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Flapjack-specific structural infrastructure for the original Inst case.
HOL proves this fact inside comp_no_shmemop rather than as a separate theorem.
All instruction constructors and arbitrary positive widths are retained. -/
theorem wInstNoShmemop {width : Nat} [NeZero width]
    (instruction : HolInst width) (frame : Nat × Nat × Nat) :
    noShmemop (wInstNative instruction frame) = true := by
  have write1 (g : Nat → HolInst width) (r : Nat) :
      noShmemop (wRegWrite1Native (fun reg => .inst (g reg)) r frame) = true :=
    wRegWrite1NoShmemop _ r frame (fun _ => rfl)
  have write21 (g : Nat → Nat → HolInst width) (r1 r2 : Nat) :
      noShmemop (wRegWrite2Native
        (fun reg2 => wRegWrite1Native (fun reg1 => .inst (g reg1 reg2)) r1 frame)
        r2 frame) = true :=
    wRegWrite2NoShmemop _ r2 frame (fun reg2 => write1 (fun reg1 => g reg1 reg2) r1)
  cases instruction with
  | arith a =>
    cases a <;> try (rename_i op d s ri; cases ri)
    all_goals simp [wInstNative, wStackLoadNoShmemop, write1, noShmemop]
  | mem op d addr =>
    cases addr
    cases op <;> simp [wInstNative, wStackLoadNoShmemop,
      write1, noShmemop]
  | fp f =>
    cases f
    all_goals
      by_cases hw : width = 64
      all_goals simp [wInstNative, hw, wStackLoadNoShmemop,
        write1, write21, noShmemop]
  | skip => rfl
  | const n c => simp [wInstNative, write1]

/-- The full original comp_no_shmemop Inst case. All original hypotheses and
output components are retained; the source guard is redundant in this case,
but is kept to give exactly the original case statement. The helper proof
covers every original instruction clause, including the FP width split. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemopInst {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (instruction : WordLangInst (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL (.inst instruction) = true)
    (compiled : compNative conf perf (.inst instruction) bs frame = (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  exact wInstNoShmemop (HolInst.ofWordLangInst instruction) frame

end Flapjack.Compiler.Backend.WordToStack.Native

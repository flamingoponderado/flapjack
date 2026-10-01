import Flapjack.Compiler.Backend.WordToStack.NativeCompile
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopHelpers
import Flapjack.Pancake.WordConvs.NotCreated

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Full original tail Call case. The optional source handler remains arbitrary
and its original source guard is retained even though this compiler branch
ignores that handler. No induction hypothesis for ignored code is required. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemopTailCall {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (destination : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (_guard : noShareInstSubprogsHOL (.call none destination args handler) = true)
    (compiled : compNative conf perf (.call none destination args handler) bs frame =
      (output, residual)) :
    noShmemop output = true := by
  have result := congrArg Prod.fst compiled
  simp only [compNative] at result
  rw [← result]
  cases destination with
  | some label =>
      simp only [callDestNative, noShmemop, Bool.true_and]
      unfold seqStackFreeNative
      split <;> rfl
  | none =>
      by_cases empty : args.length = 0
      · simp only [callDestNative, dif_pos empty, noShmemop, Bool.true_and]
        unfold seqStackFreeNative
        split <;> rfl
      · simp only [callDestNative, dif_neg empty, noShmemop, wStackLoadNoShmemop,
          Bool.true_and]
        unfold seqStackFreeNative
        split <;> rfl

end Flapjack.Compiler.Backend.WordToStack.Native

import Flapjack.Pancake.WordLang.MaxVar
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundRecursive
import Flapjack.Compiler.Backend.WordToStack.Proofs.RegisterBoundInstructions

namespace Flapjack.WordToStackProofs.RegisterBoundCompiler
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm

open Flapjack.WordToStackProofs.RegisterBoundFlat
open Flapjack.WordToStackProofs.RegisterBoundRecursive
open Flapjack.WordToStackProofs.RegisterBoundInstructions

/-- Entire original arbitrary-program register-bound theorem over actual native
compilation. All proper-subprogram hypotheses are discharged internally at the
actual threaded bitmap states. The premises are exactly the source conventions,
original minimum frame bound and false-performance guard; no target result or
safety predicate is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_reg_bound" (words_as_type_indexed_bitvec)]
theorem wordToStackRegBound {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (conventions : postAllocConventionsHOL frame.1 program = true)
    (room : 4 ≤ frame.1) (plain : perf = false) :
    regBound (compNative conf perf program bs frame).1 (frame.1 + 2) := by
  set_option tactic.fun_induction.unfolding false in
    fun_induction maxVarHOL program generalizing bs frame with
    | case8 dest args values live body l1 l2 ih =>
        exact wordToStackRegBoundCallReturn conf perf values live body l1 l2 dest args
          bs frame conventions room plain (by intros; apply ih <;> assumption)
    | case9 dest args values live body l1 l2 value handler h1 h2 ihBody ihHandler =>
        exact wordToStackRegBoundCallHandler conf perf values live body handler l1 l2 value h1 h2
          dest args bs frame conventions room plain
          (by intros; apply ihBody <;> assumption) (by intros; apply ihHandler <;> assumption)
    | case10 first second ihFirst ihSecond =>
        exact wordToStackRegBoundSeq conf perf first second bs frame conventions room plain
          (by intros; apply ihFirst <;> assumption) (by intros; apply ihSecond <;> assumption)
    | case11 body ih =>
        exact wordToStackRegBoundMustTerminate conf perf body bs frame conventions room plain
          (by intros; apply ih <;> assumption)
    | case12 cmp reg ri first second ihFirst ihSecond =>
        exact wordToStackRegBoundIf conf perf cmp reg ri first second bs frame conventions room plain
          (by intros; apply ihFirst <;> assumption) (by intros; apply ihSecond <;> assumption)
    | case26 liveIn body liveOut ih =>
        exact wordToStackRegBoundLoop conf perf liveIn liveOut body bs frame conventions room plain
          (by intros; apply ih <;> assumption)
    | case27 program =>
        cases program <;> solve_by_elim [wordToStackRegBoundBreak, wordToStackRegBoundContinue]
    | _ =>
        solve_by_elim [wordToStackRegBoundSkip, wordToStackRegBoundMove, wordToStackRegBoundInst,
          wordToStackRegBoundAssign, wordToStackRegBoundGet, wordToStackRegBoundSet,
          wordToStackRegBoundStore, wordToStackRegBoundAlloc, wordToStackRegBoundStoreConsts,
          wordToStackRegBoundRaise, wordToStackRegBoundReturn, wordToStackRegBoundBreak,
          wordToStackRegBoundContinue, wordToStackRegBoundTick, wordToStackRegBoundOpCurrHeap,
          wordToStackRegBoundLocValue, wordToStackRegBoundInstall, wordToStackRegBoundCodeBufferWrite,
          wordToStackRegBoundDataBufferWrite, wordToStackRegBoundFfi, wordToStackRegBoundShareInst, wordToStackRegBoundCallTail]

end Flapjack.WordToStackProofs.RegisterBoundCompiler

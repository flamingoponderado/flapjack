import Flapjack.Pancake.WordLang.OccurrencesExact
import Flapjack.Compiler.Backend.WordToStack.Proofs.AllocArgs.RecursiveCalls

namespace Flapjack.WordToStackProofs.AllocArgs
open Flapjack Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.StackProps Flapjack.Compiler.Encoders.Asm

/-- Full original arbitrary-program allocation-argument theorem. All recursive
case hypotheses are discharged internally, with arbitrary threaded bitmap and
frame inputs; the only source premise is the original false-performance guard. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "word_to_stack_alloc_arg" (words_as_type_indexed_bitvec)]
theorem wordToStackAllocArg {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (plain : perf = false) : allocArg (compNative conf perf program bs frame).1 := by
  set_option tactic.fun_induction.unfolding false in
  fun_induction everyVarHOL (fun _ => true) program generalizing bs frame plain with
  | case13 returns dest args handler ih =>
      rcases returns with _ | ⟨values, cutsets, body, l1, l2⟩
      · exact wordToStackAllocArgCallTail conf perf dest args handler bs frame plain
      · cases handler with
        | none =>
            exact wordToStackAllocArgCallReturn conf perf values cutsets body l1 l2
              dest args bs frame plain ih.1
        | some exception =>
            rcases exception with ⟨value, hbody, h1, h2⟩
            exact wordToStackAllocArgCallHandler conf perf values cutsets body hbody
              l1 l2 value h1 h2 dest args bs frame plain ih.1 ih.2
  | case1 => exact wordToStackAllocArgSkip conf perf bs frame plain
  | case2 => exact wordToStackAllocArgMove conf perf _ _ bs frame plain
  | case3 => exact wordToStackAllocArgInst conf perf _ bs frame plain
  | case4 => exact wordToStackAllocArgAssign conf perf _ _ bs frame plain
  | case5 => exact wordToStackAllocArgGet conf perf _ _ bs frame plain
  | case6 => exact wordToStackAllocArgStore conf perf _ _ bs frame plain
  | case7 => exact wordToStackAllocArgLocValue conf perf _ _ bs frame plain
  | case8 => exact wordToStackAllocArgInstall conf perf _ _ _ _ _ bs frame plain
  | case9 => exact wordToStackAllocArgCodeBufferWrite conf perf _ _ bs frame plain
  | case10 => exact wordToStackAllocArgDataBufferWrite conf perf _ _ bs frame plain
  | case11 => exact wordToStackAllocArgFfi conf perf _ _ _ _ _ _ bs frame plain
  | case16 => exact wordToStackAllocArgAlloc conf perf _ _ bs frame plain
  | case17 => exact wordToStackAllocArgStoreConsts conf perf _ _ _ _ _ bs frame plain
  | case18 => exact wordToStackAllocArgRaise conf perf _ bs frame plain
  | case19 => exact wordToStackAllocArgReturn conf perf _ _ bs frame plain
  | case20 => exact wordToStackAllocArgOpCurrHeap conf perf _ _ _ bs frame plain
  | case21 => exact wordToStackAllocArgTick conf perf bs frame plain
  | case22 => exact wordToStackAllocArgSet conf perf _ _ bs frame plain
  | case23 => exact wordToStackAllocArgShareInst conf perf _ _ _ bs frame plain
  | case12 body ih => exact wordToStackAllocArgMustTerminate conf perf body bs frame plain ih
  | case14 first second ihFirst ihSecond =>
      exact wordToStackAllocArgSeq conf perf first second bs frame plain ihFirst ihSecond
  | case15 cmp register right first second ihFirst ihSecond =>
      exact wordToStackAllocArgIf conf perf cmp register right first second bs frame plain ihFirst ihSecond
  | case24 liveIn body liveOut ih =>
      exact wordToStackAllocArgLoop conf perf liveIn liveOut body bs frame plain ih
  | case25 p =>
      cases p <;> grind only [wordToStackAllocArgBreak, wordToStackAllocArgContinue]

end Flapjack.WordToStackProofs.AllocArgs

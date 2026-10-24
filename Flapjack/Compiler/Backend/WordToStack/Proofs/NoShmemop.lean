import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopInstructions
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopFlatEffects
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopRecursive
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopCalls
import Flapjack.Compiler.Backend.WordToStack.Proofs.NoShmemopPrimitives

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Encoders.Asm

/-- Full original compiler preservation for every source constructor. The
original source guard and actual compiler equality are the only hypotheses;
constructor induction hypotheses are discharged by terminating recursion. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml"
  "comp_no_shmemop" (words_as_type_indexed_bitvec)]
theorem compNoShmemop {width : Nat} [NeZero width]
    (conf : AsmConfigExact width) (perf : Bool)
    (program : WordLangProgHOL (BitVec width))
    (bs : AppList (BitVec width) × Nat) (frame : Nat × Nat × Nat)
    (output : HolProg width) (residual : AppList (BitVec width) × Nat)
    (guard : noShareInstSubprogsHOL program = true)
    (compiled : compNative conf perf program bs frame = (output,residual)) :
    noShmemop output = true := by
  set_option tactic.fun_induction.unfolding false in
  fun_induction everyVarHOL (fun _ => true) program generalizing bs frame output residual with
  | case13 returns dest args handler ih =>
      rcases returns with _ | ⟨values, cutsets, body, l1, l2⟩
      · exact compNoShmemopTailCall conf perf dest args handler bs frame output residual guard compiled
      · cases handler with
        | none =>
            exact compNoShmemopReturningCall conf perf values cutsets body l1 l2
              dest args bs frame output residual guard compiled ih.1
        | some exception =>
            rcases exception with ⟨value, hbody, h1, h2⟩
            exact compNoShmemopHandledCall conf perf values cutsets body l1 l2 dest args
              value hbody h1 h2 bs frame output residual guard compiled ih.1 ih.2
  | case1 => exact compNoShmemopSkip conf perf bs frame output residual guard compiled
  | case2 => exact compNoShmemopMove conf perf _ _ bs frame output residual guard compiled
  | case3 => exact compNoShmemopInst conf perf _ bs frame output residual guard compiled
  | case4 => exact compNoShmemopAssign conf perf _ _ bs frame output residual guard compiled
  | case5 => exact compNoShmemopGet conf perf _ _ bs frame output residual guard compiled
  | case6 => exact compNoShmemopStore conf perf _ _ bs frame output residual guard compiled
  | case7 => exact compNoShmemopLocValue conf perf _ _ bs frame output residual guard compiled
  | case8 => exact compNoShmemopInstall conf perf _ _ _ _ _ bs frame output residual guard compiled
  | case9 => exact compNoShmemopCodeBufferWrite conf perf _ _ bs frame output residual guard compiled
  | case10 => exact compNoShmemopDataBufferWrite conf perf _ _ bs frame output residual guard compiled
  | case11 => exact compNoShmemopFFI conf perf _ _ _ _ _ _ bs frame output residual guard compiled
  | case16 => exact compNoShmemopAlloc conf perf _ _ bs frame output residual guard compiled
  | case17 => exact compNoShmemopStoreConsts conf perf _ _ _ _ _ bs frame output residual guard compiled
  | case18 => exact compNoShmemopRaise conf perf _ bs frame output residual guard compiled
  | case19 => exact compNoShmemopReturn conf perf _ _ bs frame output residual guard compiled
  | case20 => exact compNoShmemopOpCurrHeap conf perf _ _ _ bs frame output residual guard compiled
  | case21 => exact compNoShmemopTick conf perf bs frame output residual guard compiled
  | case22 => exact compNoShmemopSet conf perf _ _ bs frame output residual guard compiled
  | case23 => exact compNoShmemopShareInst conf perf _ _ _ bs frame output residual guard compiled
  | case12 body ih => exact compNoShmemopMustTerminate conf perf body bs frame output residual guard compiled ih
  | case14 first second ihFirst ihSecond =>
      exact compNoShmemopSeq conf perf first second bs frame output residual guard compiled ihFirst ihSecond
  | case15 cmp register right first second ihFirst ihSecond =>
      exact compNoShmemopIf conf perf cmp register right first second bs frame output residual guard compiled ihFirst ihSecond
  | case24 liveIn body liveOut ih =>
      exact compNoShmemopLoop conf perf liveIn liveOut body bs frame output residual guard compiled ih
  | case25 p =>
      cases p <;> grind only [compNoShmemopBreak, compNoShmemopContinue]

end Flapjack.Compiler.Backend.WordToStack.Native

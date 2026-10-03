import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Call
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Nonrecursive
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Inst
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Alloc
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.StoreConsts
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Install
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.FFI
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.If
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.Loop
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.JumpLower
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps.RawCall
import Flapjack.Compiler.Backend.Semantics.StackSem.EvaluateClock

namespace Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open StackSemMeasure StackSemStateOps StackSemControl

/-- Native well-founded assembly infrastructure; no separate HOL declaration. -/
private theorem bitmapMeasure {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure → ∀ (result : Option (StackSemResult width))
        (post : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (program, source) = (result, post) → CodeBitmaps source post := by
  intro measure
  induction measure using EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm r post execution
  subst hm
  cases p
  case skip  => exact Nonrecursive.evaluateCodeBitmapsSkip  s post r execution
  case halt v => exact Nonrecursive.evaluateCodeBitmapsHalt v s post r execution
  case ret v => exact Nonrecursive.evaluateCodeBitmapsRet v s post r execution
  case raise v => exact Nonrecursive.evaluateCodeBitmapsRaise v s post r execution
  case «break» v => exact Nonrecursive.evaluateCodeBitmapsBreak v s post r execution
  case «continue» v => exact Nonrecursive.evaluateCodeBitmapsContinue v s post r execution
  case get v n => exact Nonrecursive.evaluateCodeBitmapsGet v n s post r execution
  case set n v => exact Nonrecursive.evaluateCodeBitmapsSet n v s post r execution
  case opCurrHeap b d src => exact Nonrecursive.evaluateCodeBitmapsOpCurrHeap b d src s post r execution
  case tick  => exact Nonrecursive.evaluateCodeBitmapsTick  s post r execution
  case locValue a b c => exact Nonrecursive.evaluateCodeBitmapsLocValue a b c s post r execution
  case stackAlloc n => exact Nonrecursive.evaluateCodeBitmapsStackAlloc n s post r execution
  case stackFree n => exact Nonrecursive.evaluateCodeBitmapsStackFree n s post r execution
  case stackLoad a b => exact Nonrecursive.evaluateCodeBitmapsStackLoad a b s post r execution
  case stackLoadAny a b => exact Nonrecursive.evaluateCodeBitmapsStackLoadAny a b s post r execution
  case stackStore a b => exact Nonrecursive.evaluateCodeBitmapsStackStore a b s post r execution
  case stackStoreAny a b => exact Nonrecursive.evaluateCodeBitmapsStackStoreAny a b s post r execution
  case stackGetSize a => exact Nonrecursive.evaluateCodeBitmapsStackGetSize a s post r execution
  case stackSetSize a => exact Nonrecursive.evaluateCodeBitmapsStackSetSize a s post r execution
  case bitmapLoad a b => exact Nonrecursive.evaluateCodeBitmapsBitmapLoad a b s post r execution
  case codeBufferWrite a b => exact Nonrecursive.evaluateCodeBitmapsCodeBufferWrite a b s post r execution
  case dataBufferWrite a b => exact Nonrecursive.evaluateCodeBitmapsDataBufferWrite a b s post r execution
  case shMemOp op reg addr =>
    cases addr with
    | addr address offset => exact Nonrecursive.evaluateCodeBitmapsShMemOp op reg address offset s post r execution
  case inst instruction => exact evaluateCodeBitmapsInst instruction s post r execution
  case alloc register => exact evaluateCodeBitmapsAlloc register s post r execution
  case storeConsts first second stub => exact evaluateCodeBitmapsStoreConsts first second stub s post r execution
  case install a b c d e => exact evaluateCodeBitmapsInstall a b c d e s post r execution
  case ffi n a b c d e => exact FFI.evaluateCodeBitmapsFFI n a b c d e s post r execution
  case seq first second =>
    apply evaluateCodeBitmapsSeq first second s post r
    · intro res out run
      exact ih _ (seq_first_measure_lt first second s) first s rfl res out run
    · intro middle firstRun res out run
      exact ih _ (seq_second_measure_lt first second s ((none : Option (StackSemResult width)), middle)) second _ rfl res out run
    · exact execution
  case ite cmp reg operand first second =>
    apply evaluateCodeBitmapsIf cmp reg operand first second s post r
    · intro x y left right compared out res run
      exact ih _ (if_first_measure_lt cmp reg operand first second s) first s rfl res out run
    · intro x y left right compared out res run
      exact ih _ (if_second_measure_lt cmp reg operand first second s) second s rfl res out run
    · exact execution
  case loop body =>
    apply evaluateCodeBitmapsLoop body s post r
    · intro out res run
      exact ih _ (loop_body_measure_lt body s) body s rfl res out run
    · intro middle bodyResult bodyRun continues nonzero out res decrease run
      exact ih _ (lexNat_of_clock_lt decrease) (.loop body) _ rfl res out run
    · exact execution
  case jumpLower r1 r2 dest =>
    apply evaluateCodeBitmapsJumpLower r1 r2 dest s post r
    · intro x y prog left right compared lookup nonzero res out run
      exact ih _ (callee_measure_lt prog (.jumpLower r1 r2 dest) s nonzero) prog _ rfl res out run
    · exact execution
  case rawCall dest =>
    apply evaluateCodeBitmapsRawCall dest s post r
    · intro prog first body lookup sequence nonzero res out run
      exact ih _ (callee_measure_lt body (.rawCall dest) s nonzero) body _ rfl res out run
    · exact execution
  case call ret dest handler =>
    apply evaluateCodeBitmapsCall ret dest handler s post r
    · intro selected prog lookup absent nonzero res out run
      exact ih _ (callee_measure_lt prog (.call ret dest handler) s nonzero) prog _ rfl res out run
    · intro retH link l1 l2 selected prog lookup nonzero res out run
      have lower := callee_measure_lt prog (.call ret dest handler)
        (setVar link (.loc l1 l2) s) nonzero
      exact ih _ lower prog _ rfl res out run
    · intro retH link l1 l2 selected prog lookup nonzero middle calleeRun res out run
      exact ih _ (call_continuation_measure_lt retH (.call ret dest handler) s link l1 l2
        (some (StackSemResult.result (.loc l1 l2) : StackSemResult width), middle) nonzero) retH _ rfl res out run
    · intro retH link l1 l2 selected prog h hl1 hl2 lookup nonzero present middle calleeRun res out run
      exact ih _ (call_continuation_measure_lt h (.call ret dest handler) s link l1 l2
        (some (StackSemResult.exception (.loc hl1 hl2) : StackSemResult width), middle) nonzero) h _ rfl res out run
    · exact execution

namespace Full
/-- Re-export of the canonical reviewed codec; representation infrastructure. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  Flapjack.StackSemStateOps.holFmapAsFiniteSupportWitness
end Full

/-- Full original evaluator theorem: arbitrary program/state/result, with only
actual source execution as premise and all three original existential conjuncts.
Clock-first lexicographic induction discharges all constructor IHs internally;
Lean structural size is termination infrastructure, not HOL prog_size equality.
Canonical state maps and positive-width words use the named translations.
The evaluator closure inherits reals_as_rational_cuts; this theorem establishes
structural oracle/code/bitmap preservation, not numeric FP correspondence or
whole compiler correctness. -/
@[hol "cakeml/compiler/backend/semantics/stackPropsScript.sml" "evaluate_code_bitmaps"
  (fmap_as_finite_support := [regs, fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateCodeBitmaps {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (post : StackSemStateFiniteExact width C F)
    (execution : StackSemEvaluate.evaluate (program, source) = (result, post)) :
    ∃ count,
      post.compileOracle = holShiftSeq count source.compileOracle ∧
      post.code = ((List.range count).map
        (fun index => sptFromAList (source.compileOracle index).2.1)).foldl sptUnion source.code ∧
      post.bitmaps = source.bitmaps ++ ((List.range count).map
        (fun index => (source.compileOracle index).2.2)).flatten :=
  bitmapMeasure (stackSemMeasure program source) program source rfl result post execution

end Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps

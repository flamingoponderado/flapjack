import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.BasicLeaves
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.ControlLeaves
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.StackAccess
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.MemoryFfi
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.AllocationStore
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Install
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Loop
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.JumpLower
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Call
import Flapjack.Compiler.Backend.Semantics.StackSem.Measure.CallSites

namespace Flapjack.Compiler.Backend.StackRawCall.FullCompCorrect
open Flapjack Flapjack.Compiler.Backend.StackLang
open IfCase StackSemMeasure StackSemStateOps StackSemControl

/-- Well-founded assembly infrastructure for the original paired motive.
Lean structural size is used only for termination, not as a HOL size port. -/
private theorem compCorrectMeasure {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width)
      (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      ∀ (info : Spt Nat) (target post : StackSemStateFiniteExact width C F)
        (result : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (program, source) = (result, post) ∧
        result ≠ some .error ∧ stateRel info source target →
      SimulationResult (compTop info program) info target post result ∧
      SimulationResult (comp info program) info target post result := by
  intro measure
  induction measure using Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro p s hm info t post r hypothesis
  subst hm
  cases p
  case skip  => exact BasicLeaves.compCorrectSkip  info s t post r hypothesis
  case halt v => exact BasicLeaves.compCorrectHalt v info s t post r hypothesis
  case get v n => exact BasicLeaves.compCorrectGet v n info s t post r hypothesis
  case set n v => exact BasicLeaves.compCorrectSet n v info s t post r hypothesis
  case opCurrHeap b d src => exact BasicLeaves.compCorrectOpCurrHeap b d src info s t post r hypothesis
  case tick  => exact BasicLeaves.compCorrectTick  info s t post r hypothesis
  case ret v => exact ControlLeaves.compCorrectReturn v info s t post r hypothesis
  case raise v => exact ControlLeaves.compCorrectRaise v info s t post r hypothesis
  case «break» v => exact ControlLeaves.compCorrectBreak v info s t post r hypothesis
  case «continue» v => exact ControlLeaves.compCorrectContinue v info s t post r hypothesis
  case locValue a b c => exact StackAccessCase.compCorrectLocValue a b c info s t post r hypothesis
  case stackAlloc n => exact StackAccessCase.compCorrectStackAlloc n info s t post r hypothesis
  case stackFree n => exact StackAccessCase.compCorrectStackFree n info s t post r hypothesis
  case stackLoad a b => exact StackAccessCase.compCorrectStackLoad a b info s t post r hypothesis
  case stackLoadAny a b => exact StackAccessCase.compCorrectStackLoadAny a b info s t post r hypothesis
  case stackStore a b => exact StackAccessCase.compCorrectStackStore a b info s t post r hypothesis
  case stackStoreAny a b => exact StackAccessCase.compCorrectStackStoreAny a b info s t post r hypothesis
  case stackGetSize a => exact StackAccessCase.compCorrectStackGetSize a info s t post r hypothesis
  case stackSetSize a => exact StackAccessCase.compCorrectStackSetSize a info s t post r hypothesis
  case bitmapLoad a b => exact StackAccessCase.compCorrectBitmapLoad a b info s t post r hypothesis
  case codeBufferWrite a b => exact MemoryFfiCase.compCorrectCodeBufferWrite a b info s t post r hypothesis
  case dataBufferWrite a b => exact MemoryFfiCase.compCorrectDataBufferWrite a b info s t post r hypothesis
  case ffi n a b c d e => exact MemoryFfiCase.compCorrectFfi n a b c d e info s t post r hypothesis
  case alloc register => exact AllocationStoreCase.compCorrectAlloc register info s t post r hypothesis
  case storeConsts first second stub => exact AllocationStoreCase.compCorrectStoreConsts first second stub info s t post r hypothesis
  case install a b c d e => exact InstallCase.compCorrectInstall a b c d e info s t post r hypothesis
  case shMemOp op reg addr =>
    cases addr with
    | addr address offset =>
      exact MemoryFfiCase.compCorrectShMemOp op reg address offset info s t post r hypothesis
  case inst instruction =>
    have simulation : SimulationResult (comp info (.inst instruction)) info t post r := by
      simpa only [SimulationResult, Nat.add_comm] using
        evaluateCompInst instruction info s t post r hypothesis
    exact ⟨by simpa only [compTop] using simulation, simulation⟩
  case seq first second =>
    apply SeqCase.compCorrectSeq first second info s t post r
    · intro i target out res h
      exact (ih _ (seq_first_measure_lt first second s) first s rfl i target out res h).2
    · intro middle firstRun i target out res h
      have bound := StackSemEvaluateClock.evaluateClock first s none middle firstRun
      exact (ih _ (lexNat_of_le_of_size_lt bound (seq_second_size_lt first second))
        second middle rfl i target out res h).2
    · exact hypothesis
  case ite cmp reg operand first second =>
    apply IfCase.compCorrectIf cmp reg operand first second info s t post r
    · intro x y left right compared i target out res h
      exact (ih _ (if_first_measure_lt cmp reg operand first second s)
        first s rfl i target out res h).2
    · intro x y left right compared i target out res h
      exact (ih _ (if_second_measure_lt cmp reg operand first second s)
        second s rfl i target out res h).2
    · exact hypothesis
  case loop body =>
    apply LoopCase.compCorrectLoop body info s t post r
    · intro i target out res h
      exact (ih _ (loop_body_measure_lt body s) body s rfl i target out res h).2
    · intro bodyResult middle bodyRun continues nonzero i target out res h
      have lower := LoopCase.loopReentryClockLess body s middle bodyResult bodyRun nonzero
      exact (ih _ (lexNat_of_clock_lt lower) (.loop body) (decClock middle)
        rfl i target out res h).2
    · exact hypothesis
  case jumpLower r1 r2 dest =>
    apply JumpLowerCase.compCorrectJumpLower r1 r2 dest info s t post r
    · intro x y prog left right compared lookup nonzero i target out res h
      exact (ih _ (callee_measure_lt prog (.jumpLower r1 r2 dest) s nonzero)
        prog (decClock s) rfl i target out res h).1
    · exact hypothesis
  case rawCall dest =>
    apply RawCallCase.compCorrectRawCall dest info s t post r
    · intro first body lookup nonzero i target out res h
      exact (ih _ (callee_measure_lt body (.rawCall dest) s nonzero)
        body (decClock s) rfl i target out res h).2
    · exact hypothesis
  case call ret dest handler =>
    apply CallAssembly.compCorrectCall ret dest handler info s t post r
    · cases ret with
      | none =>
        intro absent prog lookup nonzero i target out res h
        exact (ih _ (callee_measure_lt prog (.call none dest handler) s nonzero)
          prog (decClock s) rfl i target out res h).1
      | some triple =>
        obtain ⟨body, link, l1, l2⟩ := triple
        refine ⟨?_, ?_, ?_⟩
        · intro prog lookup nonzero i target out res h
          have lower := callee_measure_lt prog (.call (some (body, link, l1, l2)) dest handler)
            (setVar link (.loc l1 l2) s) nonzero
          exact (ih _ lower prog (decClock (setVar link (.loc l1 l2) s))
            rfl i target out res h).1
        · intro prog lookup nonzero middle calleeRun i target out res h
          have bound := StackSemEvaluateClock.evaluateClock prog
            (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
          have lower : middle.clock < s.clock := by
            have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
            exact Nat.lt_of_le_of_lt bound decreased
          exact (ih _ (lexNat_of_clock_lt lower) body middle rfl i target out res h).2
        · intro prog handlerBody hl1 hl2 lookup nonzero present middle calleeRun i target out res h
          have bound := StackSemEvaluateClock.evaluateClock prog
            (decClock (setVar link (.loc l1 l2) s)) _ middle calleeRun
          have lower : middle.clock < s.clock := by
            have decreased := decClock_clock_lt (setVar link (.loc l1 l2) s) nonzero
            exact Nat.lt_of_le_of_lt bound decreased
          exact (ih _ (lexNat_of_clock_lt lower) handlerBody middle rfl i target out res h).2
    · exact hypothesis

/-- Reviewed codec for the actual imported state owner; representation
infrastructure with no separate HOL declaration. -/
theorem holFmapAsFiniteSupportRelationWitness_StackSemStateFiniteExact
    {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : StackSemStateBroad width C F) (h : state.FiniteSupport),
      (StackSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : StackSemStateFiniteExact width C F,
      StackSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  StackSemStateSupport.holFmapAsFiniteSupportWitness

/-- Full original comp_correct: arbitrary native program and states with only
source evaluation, nonError and the literal initial state relation as premises.
Both existential target executions and the original timeout/Halt Word2
stack-space exceptions are preserved. Clock-first well-founded induction
discharges all 34 constructors and every guarded recursive hypothesis internally.
Canonical finite maps and positive-width words use the named translations;
Spt code/info and native lists retain their original carriers. The evaluator
inherits reals_as_rational_cuts (SOUNDNESS item 8); this establishes the rawcall
pass simulation, not numeric FP correspondence or whole compiler correctness. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrect {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source target : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (hypothesis : StackSemEvaluate.evaluate (program, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    SimulationResult (compTop info program) info target post result ∧
    SimulationResult (comp info program) info target post result :=
  compCorrectMeasure (stackSemMeasure program source) program source rfl
    info target post result hypothesis

end Flapjack.Compiler.Backend.StackRawCall.FullCompCorrect

import Flapjack.Compiler.Backend.DataSpace.Proofs.TimeoutSwap

/-! Timeout resource-independence for all data-language programs. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Varying resource accounting preserves the frame size of a timeout. -/
theorem evaluate_timeout_resource_size {C F : Type} (program : DataLang.Prog)
    (state next targetNext : State C F) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (run : DataSem.evaluate program state = (some (.err (.abort .timeoutError)), next))
    (targetRun : DataSem.evaluate program { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
      (some (.err (.abort .timeoutError)), targetNext)) : next.localsSize = targetNext.localsSize := by
  have allRanks : ∀ clock weight : Nat, ∀ (program : DataLang.Prog) (state next targetNext : State C F)
      (safe : Bool) (peak : Nat) (stackMax : Option Nat), state.clock = clock → sizeOf program = weight →
      DataSem.evaluate program state = (some (.err (.abort .timeoutError)), next) →
      DataSem.evaluate program { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (some (.err (.abort .timeoutError)), targetNext) → next.localsSize = targetNext.localsSize := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock clockIH =>
      intro weight
      induction weight using Nat.strongRecOn with
      | ind weight weightIH =>
        have exprIH : ∀ (child : DataLang.Prog) (state next targetNext : State C F)
            (safe : Bool) (peak : Nat) (stackMax : Option Nat), state.clock ≤ clock → sizeOf child < weight →
            DataSem.evaluate child state = (some (.err (.abort .timeoutError)), next) →
            DataSem.evaluate child { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
              (some (.err (.abort .timeoutError)), targetNext) → next.localsSize = targetNext.localsSize := by
          intro child state next targetNext safe peak stackMax clockLe weightLt run targetRun
          rcases Nat.lt_or_eq_of_le clockLe with clockLt | clockEq
          · exact clockIH state.clock clockLt (sizeOf child) child state next targetNext safe peak stackMax rfl rfl run targetRun
          · exact weightIH (sizeOf child) weightLt child state next targetNext safe peak stackMax clockEq rfl run targetRun
        have smaller : ∀ (child : DataLang.Prog) (state next targetNext : State C F)
            (safe : Bool) (peak : Nat) (stackMax : Option Nat), state.clock < clock →
            DataSem.evaluate child state = (some (.err (.abort .timeoutError)), next) →
            DataSem.evaluate child { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
              (some (.err (.abort .timeoutError)), targetNext) → next.localsSize = targetNext.localsSize := by
          intro child state next targetNext safe peak stackMax clockLt run targetRun
          exact clockIH state.clock clockLt (sizeOf child) child state next targetNext safe peak stackMax rfl rfl run targetRun
        intro program state next targetNext safe peak stackMax stateClock measure run targetRun
        by_cases zero : state.clock = 0
        · exact evaluate_timeout_zeroClock_size program state next targetNext safe peak stackMax zero run targetRun
        · cases program with
          | skip => simp [DataSem.evaluate] at run
          | move dest src => cases read : getVar src state.locals <;> simp [DataSem.evaluate, read] at run
          | assign dest op args names => exact False.elim (evaluate_assign_ne_timeout dest op args names state next run)
          | tick => simp [DataSem.evaluate, zero] at run
          | makeSpace amount names => cases cut : cutEnv names state.locals <;> simp [DataSem.evaluate, cut] at run
          | raise name =>
            cases read : getVar name state.locals with
            | none => simp [DataSem.evaluate, read] at run
            | some value => cases jump : jumpExc state <;> simp [DataSem.evaluate, read, jump] at run
          | «return» names => cases read : DataSem.getVars names state.locals <;> simp [DataSem.evaluate, read] at run
          | seq first second =>
            rw [DataSem.evaluate, fixClock_evaluate] at run targetRun
            cases firstRun : DataSem.evaluate first state with
            | mk outcome mid =>
              rw [firstRun] at run
              cases outcome with
              | some result =>
                simp only [Prod.mk.injEq, Option.some.injEq] at run
                obtain ⟨rfl, rfl⟩ := run
                obtain ⟨matched, matchedRun, _, _⟩ := evaluate_resource_variation first state mid
                  (some (.err (.abort .timeoutError))) safe peak stackMax firstRun (by simp)
                rw [matchedRun] at targetRun
                simp only [Prod.mk.injEq] at targetRun
                obtain ⟨_, rfl⟩ := targetRun
                apply exprIH first state mid matched safe peak stackMax (by omega) ?_ firstRun matchedRun
                simp only [DataLang.Prog.seq.sizeOf_spec] at measure
                omega
              | none =>
                obtain ⟨safe', peak', max', varied⟩ := evaluate_resource_variation_normal first state mid safe peak stackMax firstRun
                rw [varied] at targetRun
                have midClock : mid.clock ≤ clock := by
                  have bound := evaluate_clock_le first state
                  rw [firstRun] at bound
                  change mid.clock ≤ state.clock at bound
                  omega
                apply exprIH second mid next targetNext safe' peak' max' midClock ?_ run targetRun
                simp only [DataLang.Prog.seq.sizeOf_spec] at measure
                omega
          | ifThenElse name yes no =>
            cases read : getVar name state.locals with
            | none => simp [DataSem.evaluate, read] at run
            | some value =>
              by_cases yesTest : isBool true value
              · have sourceBranch : DataSem.evaluate yes state = (some (.err (.abort .timeoutError)), next) := by
                  simpa [DataSem.evaluate, read, yesTest] using run
                have targetBranch : DataSem.evaluate yes { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } = (some (.err (.abort .timeoutError)), targetNext) := by
                  simpa [DataSem.evaluate, read, yesTest] using targetRun
                apply exprIH yes state next targetNext safe peak stackMax (by omega) ?_ sourceBranch targetBranch
                simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
                omega
              · by_cases noTest : isBool false value
                · have sourceBranch : DataSem.evaluate no state = (some (.err (.abort .timeoutError)), next) := by
                    simpa [DataSem.evaluate, read, yesTest, noTest] using run
                  have targetBranch : DataSem.evaluate no { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } = (some (.err (.abort .timeoutError)), targetNext) := by
                    simpa [DataSem.evaluate, read, yesTest, noTest] using targetRun
                  apply exprIH no state next targetNext safe peak stackMax (by omega) ?_ sourceBranch targetBranch
                  simp only [DataLang.Prog.ifThenElse.sizeOf_spec] at measure
                  omega
                · simp [DataSem.evaluate, read, yesTest, noTest] at run
          | force ret label src =>
            apply evaluate_force_timeout_size_step ret label src state next targetNext safe peak stackMax
            · intro body entered finished targetFinished bodySafe bodyPeak bodyMax bound bodyRun bodyTarget
              exact smaller body entered finished targetFinished bodySafe bodyPeak bodyMax (by omega) bodyRun bodyTarget
            · exact run
            · exact targetRun
          | call ret dest names handler =>
            cases ret with
            | none =>
              cases handler with
              | some pair =>
                cases read : DataSem.getVars names state.locals with
                | none => simp [DataSem.evaluate, read] at run
                | some values => cases found : findCode dest values state.code state.stackFrameSizes <;> simp [DataSem.evaluate, read, found] at run
              | none =>
                apply evaluate_tailCall_timeout_size_step dest names state next targetNext safe peak stackMax
                · intro body entered finished targetFinished bodySafe bodyPeak bodyMax bound bodyRun bodyTarget
                  exact smaller body entered finished targetFinished bodySafe bodyPeak bodyMax (by omega) bodyRun bodyTarget
                · exact run
                · exact targetRun
            | some pair =>
              obtain ⟨returns, live⟩ := pair
              cases handler with
              | none =>
                apply evaluate_nonTailCall_noHandler_timeout_size_step returns live dest names state next targetNext safe peak stackMax
                · intro body entered finished targetFinished bodySafe bodyPeak bodyMax bound bodyRun bodyTarget
                  exact smaller body entered finished targetFinished bodySafe bodyPeak bodyMax (by omega) bodyRun bodyTarget
                · exact run
                · exact targetRun
              | some pair =>
                obtain ⟨name, handlerBody⟩ := pair
                apply evaluate_nonTailCall_handler_timeout_size_step returns live dest names name handlerBody state next targetNext safe peak stackMax
                · intro body entered finished targetFinished bodySafe bodyPeak bodyMax bound bodyRun bodyTarget
                  exact smaller body entered finished targetFinished bodySafe bodyPeak bodyMax (by omega) bodyRun bodyTarget
                · exact run
                · exact targetRun
  exact allRanks state.clock (sizeOf program) program state next targetNext safe peak stackMax rfl rfl run targetRun

/-- The exact resource-field swap for timeout outcomes. -/
theorem evaluate_resource_variation_timeout {C F : Type} (program : DataLang.Prog)
    (state next : State C F) (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (run : DataSem.evaluate program state = (some (.err (.abort .timeoutError)), next)) :
    ∃ safe' peak' stackMax',
      DataSem.evaluate program { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (some (.err (.abort .timeoutError)), { next with safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }) := by
  obtain ⟨localsSize, safe', peak', stackMax', targetRun⟩ :=
    evaluate_resource_variation_control program state next (some (.err (.abort .timeoutError))) safe peak stackMax run (by simp)
  have sizeEq := evaluate_timeout_resource_size program state next
    { next with localsSize := localsSize, safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }
    safe peak stackMax run targetRun
  change next.localsSize = localsSize at sizeEq
  subst localsSize
  exact ⟨safe', peak', stackMax', by simpa using targetRun⟩

/-- Varying the resource-accounting fields preserves every non-type-error
evaluation result and all other final-state fields. This untagged lemma
still requires source evaluator and carrier correspondence review. -/
theorem evaluate_resource_variation_exact {C F : Type} (program : DataLang.Prog)
    (state next : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (safe : Bool) (peak : Nat) (stackMax : Option Nat)
    (notType : result ≠ some (.err (.abort .typeError)))
    (run : DataSem.evaluate program state = (result, next)) :
    ∃ safe' peak' stackMax',
      DataSem.evaluate program { state with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax } =
        (result, { next with safeForSpace := safe', peakHeapLength := peak', stackMax := stackMax' }) := by
  by_cases timeout : result = some (.err (.abort .timeoutError))
  · subst result
    exact evaluate_resource_variation_timeout program state next safe peak stackMax run
  · exact evaluate_resource_variation_nonTimeout program state next result safe peak stackMax run notType timeout

end Flapjack.Compiler.Backend.DataSpace

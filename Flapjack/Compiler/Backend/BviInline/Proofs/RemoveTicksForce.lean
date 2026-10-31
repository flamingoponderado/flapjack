import Flapjack.Compiler.Backend.BviInline.Proofs.RemoveTicksCases

/-! Thunk forcing for the BVI tick-removal simulation. -/
namespace Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
open BviSem
open BvlSem (Value)

/-- Flapjack infrastructure: thunk forcing is reproduced before tick
cleanup, adding the clock required to execute a cleaned callee. -/
theorem force {C F : Type} (location index : Nat) (env : List Value) (target : BviState C F)
    (calleeIH : ∀ args body, target.clock ≠ 0 → Property [body] args (BviSem.decClock 1 target)) :
    Property [.force location index] env target := by
  intro source result targetNext states run
  have refs := states.1
  have clocks := states.2.1
  cases found : env[index]? with
  | none =>
    simp [removeTicksListSource, removeTicksSource, evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run.symm
    exact ⟨0, source, by simp [evaluate, found], states⟩
  | some thunk =>
    cases thunkResult : destThunk thunk source.refs with
    | badRef =>
      simp [removeTicksListSource, removeTicksSource, evaluate, found, refs, thunkResult] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨0, source, by simp [evaluate, found, thunkResult], states⟩
    | notThunk =>
      simp [removeTicksListSource, removeTicksSource, evaluate, found, refs, thunkResult] at run
      obtain ⟨rfl, rfl⟩ := run.symm
      exact ⟨0, source, by simp [evaluate, found, thunkResult], states⟩
    | isThunk mode value =>
      cases mode with
      | evaluated =>
        simp [removeTicksListSource, removeTicksSource, evaluate, found, refs, thunkResult] at run
        obtain ⟨rfl, rfl⟩ := run.symm
        exact ⟨0, source, by simp [evaluate, found, thunkResult], states⟩
      | notEvaluated =>
        have codes := findCode_removeStateRel source target states (some location) [thunk, value]
        cases codeFound : BvlSem.findCode (some location) [thunk, value] source.code with
        | none =>
          have targetCode : BvlSem.findCode (some location) [thunk, value] target.code = none := by
            simpa [codeFound] using codes
          simp [removeTicksListSource, removeTicksSource, evaluate, found, refs, thunkResult, targetCode] at run
          obtain ⟨rfl, rfl⟩ := run.symm
          exact ⟨0, source, by simp [evaluate, found, thunkResult, codeFound], states⟩
        | some pair =>
          obtain ⟨args, body⟩ := pair
          have targetCode : BvlSem.findCode (some location) [thunk, value] target.code =
              some (args, removeTicksSource body) := by simpa [codeFound] using codes
          by_cases zero : target.clock = 0
          · have sourceZero : source.clock = 0 := by rw [← clocks, zero]
            simp [removeTicksListSource, removeTicksSource, evaluate, found, refs, thunkResult,
              targetCode, zero] at run
            obtain ⟨rfl, rfl⟩ := run.symm
            refine ⟨0, { source with clock := 0 }, ?_, ?_⟩
            simp [evaluate, found, thunkResult, codeFound, sourceZero]
            simpa [refs] using removeStateRel_with_clock source target states 0
          · have sourceNonzero : source.clock ≠ 0 := by simpa [clocks] using zero
            cases bodyRun : evaluate [removeTicksSource body] args (BviSem.decClock 1 target) with
            | mk bodyResult last =>
              have cleanRun : evaluate (removeTicksListSource [body]) args (BviSem.decClock 1 target) =
                  (bodyResult, last) := by simpa [removeTicksListSource] using bodyRun
              obtain ⟨extra, sourceLast, sourceBody, lastRel⟩ :=
                calleeIH args body zero (BviSem.decClock 1 source) bodyResult last
                  (removeStateRel_decClock source target states 1) cleanRun
              have shiftedDec : BviSem.decClock 1 { source with clock := source.clock + extra } =
                  { BviSem.decClock 1 source with clock := (BviSem.decClock 1 source).clock + extra } := by
                simp [BviSem.decClock]
                omega
              cases bodyResult with
              | val values =>
                simp [removeTicksListSource, removeTicksSource, evaluate, found, refs, thunkResult,
                  targetCode, zero, bodyRun] at run
                obtain ⟨rfl, rfl⟩ := run.symm
                refine ⟨extra, sourceLast, ?_, lastRel⟩
                simp [evaluate, found, thunkResult, codeFound, sourceNonzero, shiftedDec, sourceBody]
              | err error =>
                cases error with
                | abort reason =>
                  simp [removeTicksListSource, removeTicksSource, evaluate, found, refs, thunkResult,
                    targetCode, zero, bodyRun] at run
                  obtain ⟨rfl, rfl⟩ := run.symm
                  refine ⟨extra, sourceLast, ?_, lastRel⟩
                  simp [evaluate, found, thunkResult, codeFound, sourceNonzero, shiftedDec, sourceBody]
                | raise payload =>
                  cases payload with
                  | exn value =>
                    simp [removeTicksListSource, removeTicksSource, evaluate, found, refs, thunkResult,
                      targetCode, zero, bodyRun] at run
                    obtain ⟨rfl, rfl⟩ := run.symm
                    refine ⟨extra, sourceLast, ?_, lastRel⟩
                    simp [evaluate, found, thunkResult, codeFound, sourceNonzero, shiftedDec, sourceBody]
                  | ret values =>
                    simp [removeTicksListSource, removeTicksSource, evaluate, found, refs, thunkResult,
                      targetCode, zero, bodyRun] at run
                    obtain ⟨rfl, rfl⟩ := run.symm
                    refine ⟨extra, sourceLast, ?_, lastRel⟩
                    simp [evaluate, found, thunkResult, codeFound, sourceNonzero, shiftedDec, sourceBody]

end Flapjack.Compiler.Backend.BviInline.RemoveTicksCases

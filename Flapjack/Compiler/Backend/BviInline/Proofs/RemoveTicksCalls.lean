import Flapjack.Compiler.Backend.BviInline.Proofs.RemoveTicksForce

/-! Call cases for the BVI tick-removal simulation. -/
namespace Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
open BviSem
open BvlSem (Value)

private def callResult {C F : Type} (result : BviResult) (state : BviState C F) : EvalResult C F :=
  match result with
  | .err (.raise (.ret _)) => (.err (.abort .typeError), state)
  | other => (other, state)

/-- Flapjack infrastructure: a call without a handler can restore its
removed call ticks and the clock required by its callee. -/
theorem callNone {C F : Type} (ticks : Nat) (destination : Option Nat) (args : List Bvi.Exp)
    (env : List Value) (target : BviState C F) (argsIH : Property args env target)
    (calleeIH : ∀ values middle, evaluate (removeTicksListSource args) env target = (.val values, middle) →
      ∀ callArgs body, BvlSem.findCode destination values middle.code = some (callArgs, removeTicksSource body) →
        middle.clock ≠ 0 → Property [body] callArgs (BviSem.decClock 1 middle)) :
    Property [.call ticks destination args none] env target := by
  intro source result targetNext states run
  cases argsRun : evaluate (removeTicksListSource args) env target with
  | mk argsResult middle =>
    obtain ⟨argsExtra, sourceMiddle, sourceArgs, middleRel⟩ := argsIH source argsResult middle states argsRun
    cases argsResult with
    | err error =>
      have targetEq : (.err error, middle) = (result, targetNext) := by
        have h := run
        simp only [removeTicksListSource, removeTicksSource] at h
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        cases destination <;> exact h
      obtain ⟨rfl, rfl⟩ := targetEq.symm
      refine ⟨argsExtra, sourceMiddle, ?_, middleRel⟩
      rw [evaluate, BviSem.fixClock_evaluate, sourceArgs]
      cases destination <;> rfl
    | val values =>
      have codes := findCode_removeStateRel sourceMiddle middle middleRel destination values
      cases codeFound : BvlSem.findCode destination values sourceMiddle.code with
      | none =>
        have targetCode : BvlSem.findCode destination values middle.code = none := by simpa [codeFound] using codes
        have targetEq : (.err (.abort .typeError), middle) = (result, targetNext) := by
          have h := run
          simp only [removeTicksListSource, removeTicksSource] at h
          rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
          cases destination <;> simpa [targetCode] using h
        obtain ⟨rfl, rfl⟩ := targetEq.symm
        refine ⟨argsExtra, sourceMiddle, ?_, middleRel⟩
        rw [evaluate, BviSem.fixClock_evaluate, sourceArgs]
        cases destination <;> simp [codeFound]
      | some pair =>
        obtain ⟨callArgs, body⟩ := pair
        have targetCode : BvlSem.findCode destination values middle.code = some (callArgs, removeTicksSource body) := by
          simpa [codeFound] using codes
        by_cases zero : middle.clock = 0
        · have sourceZero : sourceMiddle.clock = 0 := by rw [← middleRel.2.1, zero]
          have targetEq : (.err (.abort .timeoutError), { middle with clock := 0 }) = (result, targetNext) := by
            have h := run
            simp only [removeTicksListSource, removeTicksSource] at h
            rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
            cases destination <;> simpa [targetCode, zero] using h
          obtain ⟨rfl, rfl⟩ := targetEq.symm
          refine ⟨argsExtra, { sourceMiddle with clock := 0 }, ?_,
            removeStateRel_with_clock sourceMiddle middle middleRel 0⟩
          rw [evaluate, BviSem.fixClock_evaluate, sourceArgs]
          cases destination <;> simp [codeFound, sourceZero]
        · have sourceNonzero : sourceMiddle.clock ≠ 0 := by simpa [middleRel.2.1] using zero
          cases calleeRun : evaluate [removeTicksSource body] callArgs (BviSem.decClock 1 middle) with
          | mk calleeResult last =>
            have cleanCallee : evaluate (removeTicksListSource [body]) callArgs (BviSem.decClock 1 middle) =
                (calleeResult, last) := by simpa [removeTicksListSource] using calleeRun
            obtain ⟨bodyExtra, sourceLast, sourceBody, lastRel⟩ :=
              calleeIH values middle argsRun callArgs body targetCode zero
                (BviSem.decClock 1 sourceMiddle) calleeResult last
                (removeStateRel_decClock sourceMiddle middle middleRel 1) cleanCallee
            have shiftedArgs := BviProps.evaluate_addClock args env
              { source with clock := source.clock + argsExtra } sourceMiddle (.val values)
                (ticks + bodyExtra) sourceArgs (by simp)
            have combinedArgs : evaluate args env { source with clock := source.clock + (argsExtra + (ticks + bodyExtra)) } =
                (.val values, { sourceMiddle with clock := sourceMiddle.clock + (ticks + bodyExtra) }) := by
              simpa [Nat.add_assoc] using shiftedArgs
            have enough : ¬sourceMiddle.clock + (ticks + bodyExtra) < ticks + 1 := by omega
            have shiftedDec : BviSem.decClock (ticks + 1)
                { sourceMiddle with clock := sourceMiddle.clock + (ticks + bodyExtra) } =
                { BviSem.decClock 1 sourceMiddle with clock := (BviSem.decClock 1 sourceMiddle).clock + bodyExtra } := by
              simp [BviSem.decClock]
              omega
            have sourcePrefix : evaluate [.call ticks destination args none] env
                { source with clock := source.clock + (argsExtra + (ticks + bodyExtra)) } =
                callResult calleeResult sourceLast := by
              rw [evaluate, BviSem.fixClock_evaluate, combinedArgs]
              cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte, codeFound, enough] <;>
                rw [BviSem.fixClock_evaluate, shiftedDec, sourceBody] <;>
                cases calleeResult with
                | val values => rfl
                | err error => cases error with
                  | abort reason => rfl
                  | raise payload => cases payload <;> rfl
            have targetPrefix : evaluate (removeTicksListSource [.call ticks destination args none]) env target =
                callResult calleeResult last := by
              simp only [removeTicksListSource, removeTicksSource]
              rw [evaluate, BviSem.fixClock_evaluate, argsRun]
              cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte, targetCode, zero,
                Nat.zero_add, Nat.lt_one_iff] <;>
                rw [BviSem.fixClock_evaluate, calleeRun] <;> cases calleeResult with
                | val values => rfl
                | err error => cases error with
                  | abort reason => rfl
                  | raise payload => cases payload <;> rfl
            rw [targetPrefix] at run
            cases calleeResult with
            | val values =>
              simp only [callResult, Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run.symm
              exact ⟨argsExtra + (ticks + bodyExtra), sourceLast, by simpa [callResult] using sourcePrefix, lastRel⟩
            | err error =>
              cases error with
              | abort reason =>
                simp only [callResult, Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run.symm
                exact ⟨argsExtra + (ticks + bodyExtra), sourceLast, by simpa [callResult] using sourcePrefix, lastRel⟩
              | raise payload =>
                cases payload with
                | exn value =>
                  simp only [callResult, Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run.symm
                  exact ⟨argsExtra + (ticks + bodyExtra), sourceLast, by simpa [callResult] using sourcePrefix, lastRel⟩
                | ret values =>
                  simp only [callResult, Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run.symm
                  exact ⟨argsExtra + (ticks + bodyExtra), sourceLast, by simpa [callResult] using sourcePrefix, lastRel⟩

end Flapjack.Compiler.Backend.BviInline.RemoveTicksCases

import Flapjack.Compiler.Backend.BviInline.Proofs.RemoveTicksForce

/-! Call cases for the BVI tick-removal simulation. -/
namespace Flapjack.Compiler.Backend.BviInline.RemoveTicksCases
open BviSem
open BvlSem (Value)

private def callResult {C F : Type} (result : BviResult) (state : BviState C F) : EvalResult C F :=
  match result with
  | .err (.raise (.ret _)) => (.err (.abort .typeError), state)
  | other => (other, state)

private noncomputable def letCallResult {C F : Type} (rets : Nat) (body : Bvi.Exp)
    (env : List Value) (result : BviResult) (state : BviState C F) : EvalResult C F :=
  match result with
  | .val _ => (.err (.abort .typeError), state)
  | .err (.raise (.ret values)) =>
    if values.length = rets then evaluate [body] (values ++ env) state else (.err (.abort .typeError), state)
  | .err error => (.err error, state)

private noncomputable def handleCallResult {C F : Type} (handler : Bvi.Exp)
    (env : List Value) (call : EvalResult C F) : EvalResult C F :=
  match call with
  | (.err (.raise (.exn value)), state) =>
    match evaluate [handler] (value :: env) state with
    | (.err (.raise (.ret _)), next) => (.err (.abort .typeError), next)
    | other => other
  | other => other

/-- Flapjack infrastructure: a direct handled call first performs the same
call as the handler-free form, then handles a raised exception if present. -/
theorem evaluate_handled_as_plain {C F : Type} (ticks destination : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env : List Value) (state middle : BviState C F) (values : List Value)
    (argsRun : evaluate args env state = (.val values, middle)) :
    evaluate [.call ticks (some destination) args (some handler)] env state =
      handleCallResult handler env (evaluate [.call ticks (some destination) args none] env state) := by
  rw [evaluate, BviSem.fixClock_evaluate, argsRun, evaluate, BviSem.fixClock_evaluate, argsRun]
  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  split <;> simp only [handleCallResult]
  all_goals repeat' split
  all_goals simp_all

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

/-- Flapjack infrastructure: let-call restores call ticks, callee clock, and
the continuation's clock while retaining the result and related state. -/
theorem letCall {C F : Type} (rets ticks destination : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (env : List Value) (target : BviState C F) (argsIH : Property args env target)
    (calleeIH : ∀ values middle, evaluate (removeTicksListSource args) env target = (.val values, middle) →
      ∀ callArgs callee, BvlSem.findCode (some destination) values middle.code = some (callArgs, removeTicksSource callee) →
        middle.clock ≠ 0 → Property [callee] callArgs (BviSem.decClock 1 middle))
    (continuationIH : ∀ returned (last : BviState C F), last.clock ≤ target.clock → Property [body] (returned ++ env) last) :
    Property [.letCall rets ticks destination args body] env target := by
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
        exact h
      obtain ⟨rfl, rfl⟩ := targetEq.symm
      refine ⟨argsExtra, sourceMiddle, ?_, middleRel⟩
      rw [evaluate, BviSem.fixClock_evaluate, sourceArgs]
    | val values =>
      have codes := findCode_removeStateRel sourceMiddle middle middleRel (some destination) values
      cases codeFound : BvlSem.findCode (some destination) values sourceMiddle.code with
      | none =>
        have targetCode : BvlSem.findCode (some destination) values middle.code = none := by simpa [codeFound] using codes
        have targetEq : (.err (.abort .typeError), middle) = (result, targetNext) := by
          have h := run
          simp only [removeTicksListSource, removeTicksSource] at h
          rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
          simpa [targetCode] using h
        obtain ⟨rfl, rfl⟩ := targetEq.symm
        refine ⟨argsExtra, sourceMiddle, ?_, middleRel⟩
        rw [evaluate, BviSem.fixClock_evaluate, sourceArgs]
        simp [codeFound]
      | some pair =>
        obtain ⟨callArgs, callee⟩ := pair
        have targetCode : BvlSem.findCode (some destination) values middle.code =
            some (callArgs, removeTicksSource callee) := by simpa [codeFound] using codes
        by_cases zero : middle.clock = 0
        · have sourceZero : sourceMiddle.clock = 0 := by rw [← middleRel.2.1, zero]
          have targetEq : (.err (.abort .timeoutError), { middle with clock := 0 }) = (result, targetNext) := by
            have h := run
            simp only [removeTicksListSource, removeTicksSource] at h
            rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
            simpa [targetCode, zero] using h
          obtain ⟨rfl, rfl⟩ := targetEq.symm
          refine ⟨argsExtra, { sourceMiddle with clock := 0 }, ?_,
            removeStateRel_with_clock sourceMiddle middle middleRel 0⟩
          rw [evaluate, BviSem.fixClock_evaluate, sourceArgs]
          simp [codeFound, sourceZero]
        · have sourceNonzero : sourceMiddle.clock ≠ 0 := by simpa [middleRel.2.1] using zero
          cases calleeRun : evaluate [removeTicksSource callee] callArgs (BviSem.decClock 1 middle) with
          | mk calleeResult last =>
            have cleanCallee : evaluate (removeTicksListSource [callee]) callArgs (BviSem.decClock 1 middle) =
                (calleeResult, last) := by simpa [removeTicksListSource] using calleeRun
            obtain ⟨calleeExtra, sourceLast, sourceCallee, lastRel⟩ :=
              calleeIH values middle argsRun callArgs callee targetCode zero
                (BviSem.decClock 1 sourceMiddle) calleeResult last
                (removeStateRel_decClock sourceMiddle middle middleRel 1) cleanCallee
            have targetPrefix : evaluate (removeTicksListSource [.letCall rets ticks destination args body]) env target =
                letCallResult rets (removeTicksSource body) env calleeResult last := by
              simp only [removeTicksListSource, removeTicksSource]
              rw [evaluate, BviSem.fixClock_evaluate, argsRun]
              simp only [targetCode, Nat.zero_add, Nat.lt_one_iff, zero, ↓reduceIte]
              rw [BviSem.fixClock_evaluate, calleeRun]
              cases calleeResult with
              | val values => rfl
              | err error => cases error with
                | abort reason => rfl
                | raise payload => cases payload <;> rfl
            rw [targetPrefix] at run
            have argsClock := BviSem.evaluate_clock_le (removeTicksListSource args) env target
            rw [argsRun] at argsClock
            simp only at argsClock
            have calleeClock := BviSem.evaluate_clock_le [removeTicksSource callee] callArgs (BviSem.decClock 1 middle)
            rw [calleeRun] at calleeClock
            have lastClock : last.clock ≤ target.clock := by
              simp only [BviSem.decClock] at calleeClock
              omega
            cases calleeResult with
            | val returned =>
              simp only [letCallResult, Prod.mk.injEq] at run
              obtain ⟨rfl, rfl⟩ := run.symm
              let extra := ticks + calleeExtra
              have shifted := BviProps.evaluate_addClock args env { source with clock := source.clock + argsExtra }
                sourceMiddle (.val values) extra sourceArgs (by simp)
              have combined : evaluate args env { source with clock := source.clock + (argsExtra + extra) } =
                  (.val values, { sourceMiddle with clock := sourceMiddle.clock + extra }) := by simpa [Nat.add_assoc] using shifted
              have enough : ¬sourceMiddle.clock + extra < ticks + 1 := by dsimp [extra]; omega
              have dec : BviSem.decClock (ticks + 1) { sourceMiddle with clock := sourceMiddle.clock + extra } =
                  { BviSem.decClock 1 sourceMiddle with clock := (BviSem.decClock 1 sourceMiddle).clock + calleeExtra } := by
                simp [BviSem.decClock, extra]; omega
              refine ⟨argsExtra + extra, sourceLast, ?_, lastRel⟩
              rw [evaluate, BviSem.fixClock_evaluate, combined]
              simp only [codeFound, enough, ↓reduceIte]
              rw [BviSem.fixClock_evaluate, dec, sourceCallee]
              rfl
            | err error =>
              cases error with
              | abort reason =>
                simp only [letCallResult, Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run.symm
                let extra := ticks + calleeExtra
                have shifted := BviProps.evaluate_addClock args env { source with clock := source.clock + argsExtra }
                  sourceMiddle (.val values) extra sourceArgs (by simp)
                have combined : evaluate args env { source with clock := source.clock + (argsExtra + extra) } =
                    (.val values, { sourceMiddle with clock := sourceMiddle.clock + extra }) := by simpa [Nat.add_assoc] using shifted
                have enough : ¬sourceMiddle.clock + extra < ticks + 1 := by dsimp [extra]; omega
                have dec : BviSem.decClock (ticks + 1) { sourceMiddle with clock := sourceMiddle.clock + extra } =
                    { BviSem.decClock 1 sourceMiddle with clock := (BviSem.decClock 1 sourceMiddle).clock + calleeExtra } := by
                  simp [BviSem.decClock, extra]; omega
                refine ⟨argsExtra + extra, sourceLast, ?_, lastRel⟩
                rw [evaluate, BviSem.fixClock_evaluate, combined]
                simp only [codeFound, enough, ↓reduceIte]
                rw [BviSem.fixClock_evaluate, dec, sourceCallee]
              | raise payload =>
                cases payload with
                | exn value =>
                  simp only [letCallResult, Prod.mk.injEq] at run
                  obtain ⟨rfl, rfl⟩ := run.symm
                  let extra := ticks + calleeExtra
                  have shifted := BviProps.evaluate_addClock args env { source with clock := source.clock + argsExtra }
                    sourceMiddle (.val values) extra sourceArgs (by simp)
                  have combined : evaluate args env { source with clock := source.clock + (argsExtra + extra) } =
                      (.val values, { sourceMiddle with clock := sourceMiddle.clock + extra }) := by simpa [Nat.add_assoc] using shifted
                  have enough : ¬sourceMiddle.clock + extra < ticks + 1 := by dsimp [extra]; omega
                  have dec : BviSem.decClock (ticks + 1) { sourceMiddle with clock := sourceMiddle.clock + extra } =
                      { BviSem.decClock 1 sourceMiddle with clock := (BviSem.decClock 1 sourceMiddle).clock + calleeExtra } := by
                    simp [BviSem.decClock, extra]; omega
                  refine ⟨argsExtra + extra, sourceLast, ?_, lastRel⟩
                  rw [evaluate, BviSem.fixClock_evaluate, combined]
                  simp only [codeFound, enough, ↓reduceIte]
                  rw [BviSem.fixClock_evaluate, dec, sourceCallee]
                | ret returned =>
                  by_cases length : returned.length = rets
                  · have continuationRun : evaluate (removeTicksListSource [body]) (returned ++ env) last = (result, targetNext) := by
                      simpa [letCallResult, length, removeTicksListSource] using run
                    obtain ⟨contExtra, sourceFinal, sourceContinuation, finalRel⟩ :=
                      continuationIH returned last lastClock sourceLast result targetNext lastRel continuationRun
                    have shiftedCallee := BviProps.evaluate_addClock [callee] callArgs
                      { BviSem.decClock 1 sourceMiddle with clock := (BviSem.decClock 1 sourceMiddle).clock + calleeExtra }
                      sourceLast (.err (.raise (.ret returned))) contExtra sourceCallee (by simp)
                    let extra := ticks + calleeExtra + contExtra
                    have shifted := BviProps.evaluate_addClock args env { source with clock := source.clock + argsExtra }
                      sourceMiddle (.val values) extra sourceArgs (by simp)
                    have combined : evaluate args env { source with clock := source.clock + (argsExtra + extra) } =
                        (.val values, { sourceMiddle with clock := sourceMiddle.clock + extra }) := by simpa [Nat.add_assoc] using shifted
                    have enough : ¬sourceMiddle.clock + extra < ticks + 1 := by dsimp [extra]; omega
                    have dec : BviSem.decClock (ticks + 1) { sourceMiddle with clock := sourceMiddle.clock + extra } =
                        { { BviSem.decClock 1 sourceMiddle with clock := (BviSem.decClock 1 sourceMiddle).clock + calleeExtra } with
                          clock := (BviSem.decClock 1 sourceMiddle).clock + calleeExtra + contExtra } := by
                      simp [BviSem.decClock, extra]; omega
                    refine ⟨argsExtra + extra, sourceFinal, ?_, finalRel⟩
                    rw [evaluate, BviSem.fixClock_evaluate, combined]
                    simp only [codeFound, enough, ↓reduceIte]
                    rw [BviSem.fixClock_evaluate, dec, shiftedCallee]
                    simp only [length, ↓reduceIte]
                    exact sourceContinuation
                  · simp only [letCallResult, length, ↓reduceIte, Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run.symm
                    let extra := ticks + calleeExtra
                    have shifted := BviProps.evaluate_addClock args env { source with clock := source.clock + argsExtra }
                      sourceMiddle (.val values) extra sourceArgs (by simp)
                    have combined : evaluate args env { source with clock := source.clock + (argsExtra + extra) } =
                        (.val values, { sourceMiddle with clock := sourceMiddle.clock + extra }) := by simpa [Nat.add_assoc] using shifted
                    have enough : ¬sourceMiddle.clock + extra < ticks + 1 := by dsimp [extra]; omega
                    have dec : BviSem.decClock (ticks + 1) { sourceMiddle with clock := sourceMiddle.clock + extra } =
                        { BviSem.decClock 1 sourceMiddle with clock := (BviSem.decClock 1 sourceMiddle).clock + calleeExtra } := by
                      simp [BviSem.decClock, extra]; omega
                    refine ⟨argsExtra + extra, sourceLast, ?_, lastRel⟩
                    rw [evaluate, BviSem.fixClock_evaluate, combined]
                    simp only [codeFound, enough, ↓reduceIte]
                    rw [BviSem.fixClock_evaluate, dec, sourceCallee]
                    simp [length]

end Flapjack.Compiler.Backend.BviInline.RemoveTicksCases

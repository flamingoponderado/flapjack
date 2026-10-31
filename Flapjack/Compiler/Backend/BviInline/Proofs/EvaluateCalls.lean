import Flapjack.Compiler.Backend.BviInline.Proofs.EvaluateCases

/-! Call cases for the BVI inliner evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviInline.EvaluateCases
open BviSem
open BvlSem (Value)

private noncomputable def letCallResult {C F : Type} (rets : Nat) (body : Bvi.Exp)
    (env : List Value) (result : BviResult) (state : BviState C F) : EvalResult C F :=
  match result with
  | .val _ => (.err (.abort .typeError), state)
  | .err (.raise (.ret values)) =>
    if values.length = rets then evaluate [body] (values ++ env) state else (.err (.abort .typeError), state)
  | .err error => (.err error, state)

private noncomputable def handlerResult {C F : Type} (handler : Bvi.Exp)
    (env : List Value) (result : BviResult) (state : BviState C F) : EvalResult C F :=
  match result with
  | .err (.raise (.exn value)) =>
    match evaluate [handler] (value :: env) state with
    | (.err (.raise (.ret _)), next) => (.err (.abort .typeError), next)
    | other => other
  | .err (.raise (.ret _)) => (.err (.abort .typeError), state)
  | other => (other, state)

/-- Flapjack infrastructure: a call without an exception handler is
simulated by the corresponding non-inlined call. -/
theorem callNone_direct {C F : Type} (ticks : Nat) (destination : Option Nat)
    (args : List Bvi.Exp) (env : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (argsIH : Property args env source)
    (calleeIH : ∀ values next, evaluate args env source = (.val values, next) →
      ∀ callArgs body, BvlSem.findCode destination values next.code = some (callArgs, body) →
        ticks + 1 ≤ next.clock → Property [body] callArgs (BviSem.decClock (ticks + 1) next))
    (target : BviState C F) (targetArgs : List Bvi.Exp)
    (states : InStateRel source target) (argsRel : List.Forall₂ (ExpRel target.code) args targetArgs)
    (notType : (evaluate [.call ticks destination args none] env source).1 ≠ .err (.abort .typeError)) :
    ∃ targetNext, evaluate [.call ticks destination targetArgs none] env target =
        ((evaluate [.call ticks destination args none] env source).1, targetNext) ∧
      InStateRel (evaluate [.call ticks destination args none] env source).2 targetNext := by
  cases argsRun : evaluate args env source with
  | mk result next =>
    have argsNotType : (evaluate args env source).1 ≠ .err (.abort .typeError) := by
      cases result with
      | val values => simp [argsRun]
      | err error =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        cases destination <;> simpa [argsRun] using h
    obtain ⟨targetNext, targetRun, nextRel⟩ := argsIH target targetArgs states argsRel argsNotType
    rw [argsRun] at targetRun nextRel
    cases result with
    | err error =>
      refine ⟨targetNext, ?_, ?_⟩
      · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
        rw [evaluate, BviSem.fixClock_evaluate, argsRun]
        cases destination <;> rfl
      · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
        cases destination <;> exact nextRel
    | val values =>
      cases codeFound : BvlSem.findCode destination values next.code with
      | none =>
        have h := notType
        rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
        cases destination <;> simp [codeFound] at h
      | some pair =>
        obtain ⟨callArgs, body⟩ := pair
        obtain ⟨targetBody, targetCode, bodyRel⟩ :=
          findCode_inStateRel next targetNext destination values callArgs body nextRel codeFound
        by_cases timeout : next.clock < ticks + 1
        · have targetTimeout : targetNext.clock < ticks + 1 := by simpa [nextRel.2.1] using timeout
          refine ⟨{ targetNext with clock := 0 }, ?_, ?_⟩
          · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
            rw [evaluate, BviSem.fixClock_evaluate, argsRun]
            cases destination <;> simp [codeFound, targetCode, timeout, targetTimeout]
          · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
            cases destination <;> simpa [codeFound, timeout] using inStateRel_with_clock next targetNext nextRel 0
        · have targetEnough : ¬targetNext.clock < ticks + 1 := by simpa [nextRel.2.1] using timeout
          have enough : ticks + 1 ≤ next.clock := by omega
          cases bodyRun : evaluate [body] callArgs (BviSem.decClock (ticks + 1) next) with
          | mk bodyResult last =>
            have bodyNotType : (evaluate [body] callArgs (BviSem.decClock (ticks + 1) next)).1 ≠
                .err (.abort .typeError) := by
              cases bodyResult with
              | val values => simp [bodyRun]
              | err error =>
                cases error with
                | raise payload => cases payload <;> simp [bodyRun]
                | abort reason =>
                  have h := notType
                  rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
                  cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                    Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte, codeFound, timeout] at h <;>
                    rw [BviSem.fixClock_evaluate, bodyRun] at h <;> simpa [bodyRun] using h
            obtain ⟨targetLast, targetBodyRun, lastRel⟩ :=
              calleeIH values next argsRun callArgs body codeFound enough
                (BviSem.decClock (ticks + 1) targetNext) [targetBody]
                (inStateRel_decClock next targetNext nextRel (ticks + 1)) (.cons bodyRel .nil) bodyNotType
            rw [bodyRun] at targetBodyRun lastRel
            cases bodyResult with
            | val values =>
              refine ⟨targetLast, ?_, ?_⟩
              · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
                rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                  Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                  codeFound, targetCode, timeout, targetEnough] <;>
                  rw [BviSem.fixClock_evaluate, BviSem.fixClock_evaluate, bodyRun, targetBodyRun]
              · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                  Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte, codeFound, timeout] <;>
                  rw [BviSem.fixClock_evaluate, bodyRun] <;> exact lastRel
            | err error =>
              cases error with
              | abort reason =>
                refine ⟨targetLast, ?_, ?_⟩
                · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
                  rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                  cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                    Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                    codeFound, targetCode, timeout, targetEnough] <;>
                    rw [BviSem.fixClock_evaluate, BviSem.fixClock_evaluate, bodyRun, targetBodyRun]
                · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                  cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                    Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte, codeFound, timeout] <;>
                    rw [BviSem.fixClock_evaluate, bodyRun] <;> exact lastRel
              | raise payload =>
                cases payload with
                | exn value =>
                  refine ⟨targetLast, ?_, ?_⟩
                  · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
                    rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                    cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                      Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                      codeFound, targetCode, timeout, targetEnough] <;>
                      rw [BviSem.fixClock_evaluate, BviSem.fixClock_evaluate, bodyRun, targetBodyRun]
                  · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                    cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                      Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte, codeFound, timeout] <;>
                      rw [BviSem.fixClock_evaluate, bodyRun] <;> exact lastRel
                | ret values =>
                  have h := notType
                  rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
                  cases destination <;> simp only [Option.isNone_none, Option.isNone_some,
                    Option.isSome_none, Bool.and_false, Bool.false_eq_true, ↓reduceIte, codeFound, timeout] at h <;>
                    rw [BviSem.fixClock_evaluate, bodyRun] at h <;> simp at h

/-- Flapjack infrastructure: a handler-free call also simulates the
inliner's replacement by a let and ticks when its cached wrapper is used. -/
theorem callNone {C F : Type} (ticks : Nat) (destination : Option Nat)
    (args : List Bvi.Exp) (env : List Value)
    (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (argsIH : Property args env source)
    (calleeIH : ∀ values next, evaluate args env source = (.val values, next) →
      ∀ callArgs body, BvlSem.findCode destination values next.code = some (callArgs, body) →
        ticks + 1 ≤ next.clock → Property [body] callArgs (BviSem.decClock (ticks + 1) next)) :
    Property [.call ticks destination args none] env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons expression rest =>
    cases rest
    cases expression with
    | callNone argsRel =>
      exact callNone_direct ticks destination args env source argsIH calleeIH target _ states argsRel notType
    | inlineCall argsRel lookup length =>
      rename_i name targetArgs arity body
      obtain ⟨targetNext, targetRun, nextRel⟩ :=
        callNone_direct ticks _ args env source argsIH calleeIH target targetArgs states argsRel notType
      have targetNotType : (evaluate [.call ticks (some name) targetArgs none] env target).1 ≠ .err (.abort .typeError) := by
        rw [targetRun]
        exact notType
      have inlined := evaluate_inlined_call ticks name targetArgs body env target (by simpa [length] using lookup) targetNotType
      exact ⟨targetNext, inlined.trans targetRun, nextRel⟩

/-- Flapjack infrastructure: let-call transfers the callee result and, when
it returns the expected number of values, evaluates the related continuation. -/
theorem letCall {C F : Type} (rets ticks destination : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (env : List Value) (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (argsIH : Property args env source)
    (calleeIH : ∀ values next, evaluate args env source = (.val values, next) →
      ∀ callArgs callee, BvlSem.findCode (some destination) values next.code = some (callArgs, callee) →
        ticks + 1 ≤ next.clock → Property [callee] callArgs (BviSem.decClock (ticks + 1) next))
    (continuationIH : ∀ values (next : BviState (Spt (Nat × Bvi.Exp) × C) F),
      next.clock ≤ source.clock → Property [body] (values ++ env) next) :
    Property [.letCall rets ticks destination args body] env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons expression rest =>
    cases rest
    cases expression with
    | letCall argsRel bodyRel =>
      rename_i targetArgs targetBody
      cases argsRun : evaluate args env source with
      | mk result next =>
        have argsNotType : (evaluate args env source).1 ≠ .err (.abort .typeError) := by
          cases result with
          | val values => simp [argsRun]
          | err error =>
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
            simpa [argsRun] using h
        obtain ⟨targetNext, targetRun, nextRel⟩ := argsIH target targetArgs states argsRel argsNotType
        rw [argsRun] at targetRun nextRel
        cases result with
        | err error =>
          refine ⟨targetNext, ?_, ?_⟩
          · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
            rw [evaluate, BviSem.fixClock_evaluate, argsRun]
          · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
            exact nextRel
        | val values =>
          cases codeFound : BvlSem.findCode (some destination) values next.code with
          | none =>
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
            simp [codeFound] at h
          | some pair =>
            obtain ⟨callArgs, callee⟩ := pair
            obtain ⟨targetCallee, targetCode, calleeRel⟩ :=
              findCode_inStateRel next targetNext (some destination) values callArgs callee nextRel codeFound
            by_cases timeout : next.clock < ticks + 1
            · have targetTimeout : targetNext.clock < ticks + 1 := by simpa [nextRel.2.1] using timeout
              refine ⟨{ targetNext with clock := 0 }, ?_, ?_⟩
              · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
                rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                simp [codeFound, targetCode, timeout, targetTimeout]
              · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                simpa [codeFound, timeout] using inStateRel_with_clock next targetNext nextRel 0
            · have targetEnough : ¬targetNext.clock < ticks + 1 := by simpa [nextRel.2.1] using timeout
              have enough : ticks + 1 ≤ next.clock := by omega
              cases calleeRun : evaluate [callee] callArgs (BviSem.decClock (ticks + 1) next) with
              | mk calleeResult last =>
                have calleeNotType : (evaluate [callee] callArgs (BviSem.decClock (ticks + 1) next)).1 ≠
                    .err (.abort .typeError) := by
                  cases calleeResult with
                  | val values => simp [calleeRun]
                  | err error =>
                    cases error with
                    | raise payload => cases payload <;> simp [calleeRun]
                    | abort reason =>
                      have h := notType
                      rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
                      simp only [codeFound, timeout, ↓reduceIte] at h
                      rw [BviSem.fixClock_evaluate, calleeRun] at h
                      simpa [calleeRun] using h
                obtain ⟨targetLast, targetCalleeRun, lastRel⟩ :=
                  calleeIH values next argsRun callArgs callee codeFound enough
                    (BviSem.decClock (ticks + 1) targetNext) [targetCallee]
                    (inStateRel_decClock next targetNext nextRel (ticks + 1)) (.cons calleeRel .nil) calleeNotType
                rw [calleeRun] at targetCalleeRun lastRel
                have sourcePrefix : evaluate [.letCall rets ticks destination args body] env source =
                    letCallResult rets body env calleeResult last := by
                  rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                  simp only [codeFound, timeout, ↓reduceIte]
                  rw [BviSem.fixClock_evaluate, calleeRun]
                  cases calleeResult with
                  | val values => rfl
                  | err error => cases error with
                    | abort reason => rfl
                    | raise payload => cases payload <;> rfl
                have targetPrefix : evaluate [.letCall rets ticks destination targetArgs targetBody] env target =
                    letCallResult rets targetBody env calleeResult targetLast := by
                  rw [evaluate, BviSem.fixClock_evaluate, targetRun]
                  simp only [targetCode, targetEnough, ↓reduceIte]
                  rw [BviSem.fixClock_evaluate, targetCalleeRun]
                  cases calleeResult with
                  | val values => rfl
                  | err error => cases error with
                    | abort reason => rfl
                    | raise payload => cases payload <;> rfl
                rw [sourcePrefix] at notType ⊢
                rw [targetPrefix]
                cases calleeResult with
                | val returned => simp [letCallResult] at notType
                | err error =>
                  cases error with
                  | abort reason => exact ⟨targetLast, rfl, lastRel⟩
                  | raise payload =>
                    cases payload with
                    | exn value => exact ⟨targetLast, rfl, lastRel⟩
                    | ret returned =>
                      by_cases length : returned.length = rets
                      · have continuationNotType : (evaluate [body] (returned ++ env) last).1 ≠
                            .err (.abort .typeError) := by simpa [letCallResult, length] using notType
                        have argsClock := BviSem.evaluate_clock_le args env source
                        rw [argsRun] at argsClock
                        simp only at argsClock
                        have calleeClock := BviSem.evaluate_clock_le [callee] callArgs (BviSem.decClock (ticks + 1) next)
                        rw [calleeRun] at calleeClock
                        have clockBound : last.clock ≤ source.clock := by
                          simp only [BviSem.decClock] at calleeClock
                          omega
                        have afterArgs := (evaluate_expRel_mono targetArgs env target targetNext (.val values)
                          (by simpa using targetRun)).1 _ _ bodyRel
                        have afterCallee := (evaluate_expRel_mono [targetCallee] callArgs
                          (BviSem.decClock (ticks + 1) targetNext) targetLast (.err (.raise (.ret returned)))
                          (by simpa using targetCalleeRun)).1 _ _ (by simpa [BviSem.decClock] using afterArgs)
                        obtain ⟨targetFinal, targetContinuation, finalRel⟩ :=
                          continuationIH returned last clockBound targetLast [targetBody] lastRel
                            (.cons afterCallee .nil) continuationNotType
                        exact ⟨targetFinal, by simpa [letCallResult, length] using targetContinuation,
                          by simpa [letCallResult, length] using finalRel⟩
                      · simp [letCallResult, length] at notType

/-- Flapjack infrastructure: direct calls with handlers transfer related
callee and handler evaluations, including exceptions and clock changes. -/
theorem callSome {C F : Type} (ticks destination : Nat) (args : List Bvi.Exp)
    (handler : Bvi.Exp) (env : List Value) (source : BviState (Spt (Nat × Bvi.Exp) × C) F)
    (argsIH : Property args env source)
    (calleeIH : ∀ values next, evaluate args env source = (.val values, next) →
      ∀ callArgs callee, BvlSem.findCode (some destination) values next.code = some (callArgs, callee) →
        ticks + 1 ≤ next.clock → Property [callee] callArgs (BviSem.decClock (ticks + 1) next))
    (handlerIH : ∀ value (next : BviState (Spt (Nat × Bvi.Exp) × C) F),
      next.clock ≤ source.clock → Property [handler] (value :: env) next) :
    Property [.call ticks (some destination) args (some handler)] env source := by
  intro target ys states expressions notType
  cases expressions with
  | cons expression rest =>
    cases rest
    cases expression with
    | callSome argsRel handlerRel =>
      rename_i targetArgs targetHandler
      cases argsRun : evaluate args env source with
      | mk result next =>
        have argsNotType : (evaluate args env source).1 ≠ .err (.abort .typeError) := by
          cases result with
          | val values => simp [argsRun]
          | err error =>
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
            simpa [argsRun] using h
        obtain ⟨targetNext, targetRun, nextRel⟩ := argsIH target targetArgs states argsRel argsNotType
        rw [argsRun] at targetRun nextRel
        cases result with
        | err error =>
          refine ⟨targetNext, ?_, ?_⟩
          · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
            rw [evaluate, BviSem.fixClock_evaluate, argsRun]
            rfl
          · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
            exact nextRel
        | val values =>
          cases codeFound : BvlSem.findCode (some destination) values next.code with
          | none =>
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
            simp [codeFound] at h
          | some pair =>
            obtain ⟨callArgs, callee⟩ := pair
            obtain ⟨targetCallee, targetCode, calleeRel⟩ :=
              findCode_inStateRel next targetNext (some destination) values callArgs callee nextRel codeFound
            by_cases timeout : next.clock < ticks + 1
            · have targetTimeout : targetNext.clock < ticks + 1 := by simpa [nextRel.2.1] using timeout
              refine ⟨{ targetNext with clock := 0 }, ?_, ?_⟩
              · rw [evaluate, BviSem.fixClock_evaluate, targetRun]
                rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                simp [codeFound, targetCode, timeout, targetTimeout]
              · rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                simpa [codeFound, timeout] using inStateRel_with_clock next targetNext nextRel 0
            · have targetEnough : ¬targetNext.clock < ticks + 1 := by simpa [nextRel.2.1] using timeout
              have enough : ticks + 1 ≤ next.clock := by omega
              cases calleeRun : evaluate [callee] callArgs (BviSem.decClock (ticks + 1) next) with
              | mk calleeResult last =>
                have calleeNotType : (evaluate [callee] callArgs (BviSem.decClock (ticks + 1) next)).1 ≠
                    .err (.abort .typeError) := by
                  cases calleeResult with
                  | val values => simp [calleeRun]
                  | err error =>
                    cases error with
                    | raise payload => cases payload <;> simp [calleeRun]
                    | abort reason =>
                      have h := notType
                      rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
                      simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
                        codeFound, timeout] at h
                      rw [BviSem.fixClock_evaluate, calleeRun] at h
                      simpa [calleeRun] using h
                obtain ⟨targetLast, targetCalleeRun, lastRel⟩ :=
                  calleeIH values next argsRun callArgs callee codeFound enough
                    (BviSem.decClock (ticks + 1) targetNext) [targetCallee]
                    (inStateRel_decClock next targetNext nextRel (ticks + 1)) (.cons calleeRel .nil) calleeNotType
                rw [calleeRun] at targetCalleeRun lastRel
                have sourcePrefix : evaluate [.call ticks (some destination) args (some handler)] env source =
                    handlerResult handler env calleeResult last := by
                  rw [evaluate, BviSem.fixClock_evaluate, argsRun]
                  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, codeFound, timeout]
                  rw [BviSem.fixClock_evaluate, calleeRun]
                  cases calleeResult with
                  | val values => rfl
                  | err error => cases error with
                    | abort reason => rfl
                    | raise payload => cases payload <;> rfl
                have targetPrefix : evaluate [.call ticks (some destination) targetArgs (some targetHandler)] env target =
                    handlerResult targetHandler env calleeResult targetLast := by
                  rw [evaluate, BviSem.fixClock_evaluate, targetRun]
                  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte, targetCode, targetEnough]
                  rw [BviSem.fixClock_evaluate, targetCalleeRun]
                  cases calleeResult with
                  | val values => rfl
                  | err error => cases error with
                    | abort reason => rfl
                    | raise payload => cases payload <;> rfl
                rw [sourcePrefix] at notType ⊢
                rw [targetPrefix]
                cases calleeResult with
                | val returned => exact ⟨targetLast, rfl, lastRel⟩
                | err error =>
                  cases error with
                  | abort reason => exact ⟨targetLast, rfl, lastRel⟩
                  | raise payload =>
                    cases payload with
                    | ret returned => simp [handlerResult] at notType
                    | exn value =>
                      cases handlerRun : evaluate [handler] (value :: env) last with
                      | mk handlerRes final =>
                        have handlerNotType : (evaluate [handler] (value :: env) last).1 ≠
                            .err (.abort .typeError) := by
                          cases handlerRes with
                          | val values => simp [handlerRun]
                          | err error =>
                            cases error with
                            | raise payload => cases payload <;> simp [handlerRun]
                            | abort reason => simpa [handlerResult, handlerRun] using notType
                        have argsClock := BviSem.evaluate_clock_le args env source
                        rw [argsRun] at argsClock
                        simp only at argsClock
                        have calleeClock := BviSem.evaluate_clock_le [callee] callArgs (BviSem.decClock (ticks + 1) next)
                        rw [calleeRun] at calleeClock
                        have clockBound : last.clock ≤ source.clock := by
                          simp only [BviSem.decClock] at calleeClock
                          omega
                        have afterArgs := (evaluate_expRel_mono targetArgs env target targetNext (.val values)
                          (by simpa using targetRun)).1 _ _ handlerRel
                        have afterCallee := (evaluate_expRel_mono [targetCallee] callArgs
                          (BviSem.decClock (ticks + 1) targetNext) targetLast (.err (.raise (.exn value)))
                          (by simpa using targetCalleeRun)).1 _ _ (by simpa [BviSem.decClock] using afterArgs)
                        obtain ⟨targetFinal, targetHandlerRun, finalRel⟩ :=
                          handlerIH value last clockBound targetLast [targetHandler] lastRel
                            (.cons afterCallee .nil) handlerNotType
                        rw [handlerRun] at targetHandlerRun finalRel
                        cases handlerRes with
                        | val values => exact ⟨targetFinal, by simp [handlerResult, handlerRun, targetHandlerRun],
                            by simpa [handlerResult, handlerRun] using finalRel⟩
                        | err error =>
                          cases error with
                          | abort reason => exact ⟨targetFinal, by simp [handlerResult, handlerRun, targetHandlerRun],
                              by simpa [handlerResult, handlerRun] using finalRel⟩
                          | raise payload =>
                            cases payload with
                            | exn value => exact ⟨targetFinal, by simp [handlerResult, handlerRun, targetHandlerRun],
                                by simpa [handlerResult, handlerRun] using finalRel⟩
                            | ret values => simp [handlerResult, handlerRun] at notType

end Flapjack.Compiler.Backend.BviInline.EvaluateCases

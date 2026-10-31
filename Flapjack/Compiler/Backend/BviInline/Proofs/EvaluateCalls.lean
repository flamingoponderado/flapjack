import Flapjack.Compiler.Backend.BviInline.Proofs.EvaluateCases

/-! Call cases for the BVI inliner evaluation simulation. -/
namespace Flapjack.Compiler.Backend.BviInline.EvaluateCases
open BviSem
open BvlSem (Value)

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

end Flapjack.Compiler.Backend.BviInline.EvaluateCases

import Flapjack.Compiler.Backend.BviInline.Proofs.ExpandInduction

/-! Evaluation of an inlined direct call. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem

/-- Flapjack infrastructure: replacing a direct call with the inliner's let
and ticks preserves its evaluation when the original call does not type-error.
The source-shaped result remains untagged pending HOL carrier review. -/
theorem evaluate_inlined_call {C F : Type} (ticks name : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (env : List Value) (state : BviState C F)
    (lookup : sptLookup name state.code = some (args.length, body))
    (notType : (evaluate [.call ticks (some name) args none] env state).1 ≠ .err (.abort .typeError)) :
    evaluate [.let args (mkTick (ticks + 1) body)] env state =
      evaluate [.call ticks (some name) args none] env state := by
  cases argsRun : evaluate args env state with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [evaluate, BviSem.fixClock_evaluate, argsRun]
      simp
      rw [evaluate, BviSem.fixClock_evaluate, argsRun]
      simp
    | val values =>
      have valuesLength : values.length = args.length := BviSem.evaluate_length args env state middle values argsRun
      have subset := BviProps.evaluate_code_mono args env state middle (.val values) argsRun
      have present : sptMem name state.code := (sptMem_iff_lookup name state.code).2 ⟨_, lookup⟩
      have foundLookup : sptLookup name middle.code = some (values.length, body) := by
        rw [valuesLength]
        exact (subset name present).2.trans lookup
      have found : findCode (some name) values middle.code = some (values, body) := by
        simp [findCode, foundLookup]
      rw [evaluate, BviSem.fixClock_evaluate, argsRun]
      simp only
      rw [evaluate_mkTick]
      rw [evaluate, BviSem.fixClock_evaluate, argsRun]
      simp only [Option.isNone_some, Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte, found]
      by_cases timeout : middle.clock < ticks + 1
      · simp [timeout]
      · simp only [timeout, ↓reduceIte]
        rw [BviSem.fixClock_evaluate]
        cases bodyRun : evaluate [body] values (BviSem.decClock (ticks + 1) middle) with
        | mk result final =>
          have bodyNotType : (evaluate [body] values (BviSem.decClock (ticks + 1) middle)).1 ≠
              .err (.abort .typeError) := by
            intro bad
            rw [bodyRun] at bad
            simp at bad
            subst result
            have h := notType
            rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
            simp only [Option.isNone_some, Option.isSome_none, Bool.false_and, Bool.false_eq_true,
              ↓reduceIte, found, timeout] at h
            rw [BviSem.fixClock_evaluate, bodyRun] at h
            simp at h
          have expanded := ExpandEnv.evaluate_expand_env [body] values env (BviSem.decClock (ticks + 1) middle) bodyNotType
          rw [expanded, bodyRun]
          cases result with
          | val values => rfl
          | err error =>
            cases error with
            | abort reason => rfl
            | raise payload =>
              cases payload with
              | exn value => rfl
              | ret values =>
                have h := notType
                rw [evaluate, BviSem.fixClock_evaluate, argsRun] at h
                simp only [Option.isNone_some, Option.isSome_none, Bool.false_and, Bool.false_eq_true,
                  ↓reduceIte, found, timeout] at h
                rw [BviSem.fixClock_evaluate, bodyRun] at h
                simp at h

end Flapjack.Compiler.Backend.BviInline

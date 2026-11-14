module

public import Flapjack.Compiler.Backend.BviInline.Proofs.ExpandInduction
public import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList

@[expose] public section

/-! Evaluation of an inlined direct call. -/
namespace Flapjack.Compiler.Backend.BviInline
open BviSem BvlSem

namespace InlinedCallCarrier
/-- The canonical BVI reference-map representation has a roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : BviSem.BviStateBroad C F, (BviSem.BviState.ofBroad s).toBroad = s) ∧
      (∀ s : BviSem.BviState C F, BviSem.BviState.ofBroad s.toBroad = s) :=
  BviSem.holFmapAsFiniteSupportWitness
end InlinedCallCarrier

/-- Replacing a direct call with the inliner's let and ticks preserves its
evaluation when the original call does not type-error. The evaluator inherits
the real-model assumption documented in SOUNDNESS item 8. -/
@[hol "cakeml/compiler/backend/proofs/bvi_inlineProofScript.sml" "evaluate_inlined_call"
  (fmap_as_finite_support := [refs])]
theorem evaluate_inlined_call {C F : Type} (ticks name : Nat) (args : List Bvi.Exp)
    (body : Bvi.Exp) (env : List Value) (state : BviState C F)
    (premises : sptLookup name state.code = some (args.length, body) ∧
      (evaluateTuple ([.call ticks (some name) args none], env, state)).1 ≠ .err (.abort .typeError)) :
    evaluateTuple ([.let args (mkTick (ticks + 1) body)], env, state) =
      evaluateTuple ([.call ticks (some name) args none], env, state) := by
  obtain ⟨lookup, notType⟩ := premises
  simp only [evaluateTuple] at notType ⊢
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
          have expanded := ExpandEnv.evaluate_expand_env [body] values (BviSem.decClock (ticks + 1) middle) env bodyNotType
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

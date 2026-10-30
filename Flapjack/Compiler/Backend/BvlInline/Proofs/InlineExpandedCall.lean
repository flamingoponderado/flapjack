import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineDirectCall
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateExpandEnv

/-! The inlined Call/Let case of BVL evaluation. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps Flapjack.SemanticPrimitivesHOL

namespace InlineExpandedCallCarrier
/-- Canonical BVL reference-map state representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InlineExpandedCallCarrier

/-- The inlined Call/Let expression-relation case of the BVL simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_inlineCall {C F : Type} (limit ticks name : Nat)
    (args args' : List Bvl.Exp) (inlined : Bvl.Exp) (env : List BvlSem.Value)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (argsIH : ∀ (s last : State (Spt (Nat × Bvl.Exp) × C) F) (t : State C F)
      (res : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit s t → ExpRel s.code args args' →
      evaluateTuple (args, env, s) = (res, last) → res ≠ .err (.abort .typeError) →
      ∃ targetLast, evaluateTuple (args', env, t) = (res, targetLast) ∧ inStateRel limit last targetLast)
    (bodyIH : ∀ (middle last : State (Spt (Nat × Bvl.Exp) × C) F) (targetMiddle : State C F)
      (values : List BvlSem.Value) (body body' : Bvl.Exp)
      (res : Result (List BvlSem.Value) BvlSem.Value),
      middle.clock ≤ source.clock → ticks + 1 ≤ middle.clock →
      inStateRel limit middle targetMiddle → ExpRel middle.code [body] [body'] →
      evaluateTuple ([body], values, decClock (ticks + 1) middle) = (res, last) →
      res ≠ .err (.abort .typeError) →
      ∃ targetLast, evaluateTuple ([body'], values, decClock (ticks + 1) targetMiddle) = (res, targetLast) ∧
        inStateRel limit last targetLast)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (expressions : ExpRel source.code [.call ticks (some name) args] [.let args' inlined])
    (run : evaluateTuple ([.call ticks (some name) args], env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.let args' inlined], env, target) =
      (result, targetFinal) ∧ inStateRel limit final targetFinal := by
  cases expressions with
  | inlineCall argsRel codeFound bodyRel =>
    rename_i arity body body'
    simp only [evaluateTuple] at run
    rw [evaluate, fixClock_evaluate] at run
    cases argsRun : evaluate args env source with
    | mk argsResult middle =>
      rw [argsRun] at run
      have bound : middle.clock ≤ source.clock := by
        have h := evaluate_clock_le args env source
        simpa [argsRun] using h
      have argsNotType : argsResult ≠ .err (.abort .typeError) := by
        cases argsResult with
        | val values => simp
        | err error =>
          simp at run
          rcases run with ⟨rfl, _⟩
          exact notTypeError
      obtain ⟨targetMiddle, targetArgs, middleRel⟩ :=
        argsIH source middle target argsResult related argsRel argsRun argsNotType
      change evaluate args' env target = _ at targetArgs
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨targetMiddle, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetArgs], middleRel⟩
      | val values =>
        have growth := evaluateMono args env source (.val values) middle argsRun
        have codeFound' := (sptSubsptLookup source.code middle.code).1 growth _ _ codeFound
        have bodyRel' := subsptExpRel source.code middle.code _ _ growth bodyRel
        by_cases arityMatch : values.length = arity
        · simp [findCode, codeFound', arityMatch] at run
          by_cases timeout : middle.clock < ticks + 1
          · have targetTimeout : targetMiddle.clock < ticks + 1 := by simpa [middleRel.2.2.1] using timeout
            simp [timeout] at run
            rcases run with ⟨rfl, rfl⟩
            refine ⟨{ targetMiddle with clock := 0 }, ?_, ?_⟩
            · rw [evaluateTuple, evaluate, fixClock_evaluate, targetArgs]
              change evaluateTuple ([Bvl.mkTick (ticks + 1) body'], values ++ env, targetMiddle) = _
              rw [evaluateMkTick]
              simp [targetTimeout]
            · simpa [inStateRel] using And.intro middleRel.1 (And.intro middleRel.2.1 middleRel.2.2.2)
          · have targetEnough : ¬targetMiddle.clock < ticks + 1 := by simpa [middleRel.2.2.1] using timeout
            have enough : ticks + 1 ≤ middle.clock := Nat.le_of_not_gt timeout
            simp [timeout] at run
            obtain ⟨targetFinal, targetBody, finalRel⟩ :=
              bodyIH middle final targetMiddle values body body' result bound enough middleRel bodyRel' run notTypeError
            have targetNotType : (evaluateTuple ([body'], values, decClock (ticks + 1) targetMiddle)).1 ≠
                .err (.abort .typeError) := by rw [targetBody]; exact notTypeError
            have expanded := evaluateExpandEnv [body'] values (decClock (ticks + 1) targetMiddle) env targetNotType
            refine ⟨targetFinal, ?_, finalRel⟩
            rw [evaluateTuple, evaluate, fixClock_evaluate, targetArgs]
            change evaluateTuple ([Bvl.mkTick (ticks + 1) body'], values ++ env, targetMiddle) = _
            rw [evaluateMkTick]
            simp only [targetEnough, if_false]
            exact expanded.trans targetBody
        · simp [findCode, codeFound', arityMatch] at run
          exact False.elim (notTypeError run.1.symm)

end Flapjack.Compiler.Backend.BvlInline.Proofs

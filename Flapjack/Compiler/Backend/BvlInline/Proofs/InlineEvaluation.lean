import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineApply
import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineCall
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL

/-! Initial cases of the BVL inlining evaluator simulation. The full theorem
also requires dynamic installation and the recursive expression cases. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.SemanticPrimitivesHOL

namespace InlineEvaluationCarrier
/-- The canonical BVL reference-map state representation roundtrips. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : Flapjack.Compiler.Backend.BvlSem.State C F, State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness
end InlineEvaluationCarrier

/-- The empty-expression-list case of the inlining simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_nil {C F : Type} (limit : Nat) (env : List BvlSem.Value)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target) (_expressions : ExpRel source.code [] [])
    (run : evaluateTuple ([], env, source) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  simp [evaluateTuple, evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  exact ⟨target, by simp [evaluateTuple, evaluate], related⟩

/-- The variable case of the inlining simulation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_var {C F : Type} (limit index : Nat) (env : List BvlSem.Value)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (_expressions : ExpRel source.code [.var index] [.var index])
    (run : evaluateTuple ([.var index], env, source) = (result, final))
    (_notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.var index], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  simp only [evaluateTuple] at run
  cases found : env[index]? <;> simp [evaluate, found] at run
  all_goals rcases run with ⟨rfl, rfl⟩
  all_goals exact ⟨target, by simp [evaluateTuple, evaluate, found], related⟩

/-- The tick case of the inlining simulation, using the body induction
hypothesis with the original relation and non-type-error premises. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_tick {C F : Type} (limit : Nat) (body body' : Bvl.Exp)
    (env : List BvlSem.Value)
    (bodyIH : ∀ (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code [body] [body'] →
      evaluateTuple ([body], env, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple ([body'], env, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (expressions : ExpRel source.code [.tick body] [.tick body'])
    (run : evaluateTuple ([.tick body], env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.tick body'], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  cases expressions with
  | tick bodyRel =>
    have clocks := (inStateRel_fields limit source target related).2.2.1
    by_cases zero : source.clock = 0
    · have targetZero : target.clock = 0 := clocks.trans zero
      simp [evaluateTuple, evaluate, zero] at run
      rcases run with ⟨rfl, rfl⟩
      exact ⟨target, by simp [evaluateTuple, evaluate, targetZero], related⟩
    · have targetNonzero : target.clock ≠ 0 := by simpa [clocks] using zero
      have bodyRun : evaluateTuple ([body], env, decClock 1 source) = (result, final) := by
        simpa [evaluateTuple, evaluate, zero] using run
      obtain ⟨targetFinal, targetRun, finalRel⟩ := bodyIH (decClock 1 source) final
        (decClock 1 target) result (inStateRel_decClock limit 1 source target related)
        (by simpa [decClock] using bodyRel) bodyRun notTypeError
      exact ⟨targetFinal, by simpa [evaluateTuple, evaluate, targetNonzero] using targetRun, finalRel⟩

/-- The Raise case of the inlining simulation, using the original body
induction hypothesis. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_raise {C F : Type} (limit : Nat) (body body' : Bvl.Exp)
    (env : List BvlSem.Value)
    (bodyIH : ∀ (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code [body] [body'] →
      evaluateTuple ([body], env, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple ([body'], env, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (expressions : ExpRel source.code [.raise body] [.raise body'])
    (run : evaluateTuple ([.raise body], env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.raise body'], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  cases expressions with
  | raise bodyRel =>
    simp only [evaluateTuple] at run
    rw [evaluate] at run
    cases bodyRun : evaluate [body] env source with
    | mk bodyResult bodyFinal =>
      rw [bodyRun] at run
      have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
        cases bodyResult with
        | val values => simp
        | err error =>
          simp at run
          rcases run with ⟨rfl, _⟩
          exact notTypeError
      obtain ⟨targetFinal, targetRun, finalRel⟩ := bodyIH source bodyFinal target bodyResult
        related bodyRel (by simpa [evaluateTuple] using bodyRun) bodyNotType
      change evaluate [body'] env target = _ at targetRun
      refine ⟨targetFinal, ?_, ?_⟩
      · rw [evaluateTuple, evaluate, targetRun]
        cases bodyResult <;> simp_all
      · cases bodyResult <;> simp_all

end Flapjack.Compiler.Backend.BvlInline.Proofs

import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineApply
import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineCall
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateCodeFull

/-! Initial cases of the BVL inlining evaluator simulation. The full theorem
also requires dynamic installation and the recursive expression cases. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Flapjack.Compiler.Backend.BvlSem Flapjack.Compiler.Backend.BvlProps Flapjack.SemanticPrimitivesHOL

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

/-- The multi-expression case of the inlining simulation, using the head and
tail induction hypotheses and preservation of the source code tree. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_cons {C F : Type} (limit : Nat)
    (first second first' second' : Bvl.Exp) (rest rest' : List Bvl.Exp)
    (env : List BvlSem.Value)
    (headIH : ∀ (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code [first] [first'] →
      evaluateTuple ([first], env, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple ([first'], env, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (tailIH : ∀ (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code (second :: rest) (second' :: rest') →
      evaluateTuple (second :: rest, env, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple (second' :: rest', env, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (expressions : ExpRel source.code (first :: second :: rest) (first' :: second' :: rest'))
    (run : evaluateTuple (first :: second :: rest, env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple (first' :: second' :: rest', env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  cases expressions with
  | cons headRel tailRel =>
    simp only [evaluateTuple] at run
    rw [evaluate, fixClock_evaluate] at run
    cases headRun : evaluate [first] env source with
    | mk headResult middle =>
      rw [headRun] at run
      have headNotType : headResult ≠ .err (.abort .typeError) := by
        cases headResult with
        | val values => simp
        | err error =>
          simp at run
          rcases run with ⟨rfl, _⟩
          exact notTypeError
      have headTuple : evaluateTuple ([first], env, source) = (headResult, middle) := headRun
      obtain ⟨targetMiddle, targetHead, middleRel⟩ :=
        headIH source middle target headResult related headRel headTuple headNotType
      change evaluate [first'] env target = _ at targetHead
      cases headResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨targetMiddle, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetHead], middleRel⟩
      | val values =>
        have growth := evaluateMono [first] env source (.val values) middle headTuple
        have tailRel' := subsptExpRel source.code middle.code (second :: rest) (second' :: rest') growth tailRel
        cases tailRun : evaluate (second :: rest) env middle with
        | mk tailResult tailFinal =>
          rw [tailRun] at run
          have tailNotType : tailResult ≠ .err (.abort .typeError) := by
            cases tailResult with
            | val vals => simp
            | err error =>
              simp at run
              rcases run with ⟨rfl, _⟩
              exact notTypeError
          obtain ⟨targetFinal, targetTail, finalRel⟩ := tailIH middle tailFinal targetMiddle tailResult
            middleRel tailRel' (by simpa [evaluateTuple] using tailRun) tailNotType
          change evaluate (second' :: rest') env targetMiddle = _ at targetTail
          refine ⟨targetFinal, ?_, ?_⟩
          · rw [evaluateTuple, evaluate, fixClock_evaluate, targetHead, targetTail]
            cases tailResult <;> simp_all
          · cases tailResult <;> simp_all

end Flapjack.Compiler.Backend.BvlInline.Proofs

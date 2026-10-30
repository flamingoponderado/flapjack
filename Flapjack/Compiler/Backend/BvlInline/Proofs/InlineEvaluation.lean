import Flapjack.Compiler.Backend.BvlInline.Proofs.InstallApply
import Flapjack.Compiler.Backend.BvlInline.Proofs.InlineCall
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.BvlProps.EvaluateCodeFull

/-! Cases of the BVL inlining evaluator simulation. The full theorem also
requires the remaining recursive expression cases. -/
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

/-- The Let case of the inlining simulation, composing the binding and body
induction hypotheses across possible code growth. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_let {C F : Type} (limit : Nat)
    (bindings bindings' : List Bvl.Exp) (body body' : Bvl.Exp) (env : List BvlSem.Value)
    (bindingsIH : ∀ (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code bindings bindings' →
      evaluateTuple (bindings, env, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple (bindings', env, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (bodyIH : ∀ (bodyEnv : List BvlSem.Value)
      (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code [body] [body'] →
      evaluateTuple ([body], bodyEnv, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple ([body'], bodyEnv, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (expressions : ExpRel source.code [.let bindings body] [.let bindings' body'])
    (run : evaluateTuple ([.let bindings body], env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.let bindings' body'], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  cases expressions with
  | letExp bindingsRel bodyRel =>
    simp only [evaluateTuple] at run
    rw [evaluate, fixClock_evaluate] at run
    cases bindingsRun : evaluate bindings env source with
    | mk bindingsResult middle =>
      rw [bindingsRun] at run
      have bindingsNotType : bindingsResult ≠ .err (.abort .typeError) := by
        cases bindingsResult with
        | val values => simp
        | err error =>
          simp at run
          rcases run with ⟨rfl, _⟩
          exact notTypeError
      have bindingsTuple : evaluateTuple (bindings, env, source) = (bindingsResult, middle) := bindingsRun
      obtain ⟨targetMiddle, targetBindings, middleRel⟩ :=
        bindingsIH source middle target bindingsResult related bindingsRel bindingsTuple bindingsNotType
      change evaluate bindings' env target = _ at targetBindings
      cases bindingsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨targetMiddle, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetBindings], middleRel⟩
      | val values =>
        have growth := evaluateMono bindings env source (.val values) middle bindingsTuple
        have bodyRel' := subsptExpRel source.code middle.code [body] [body'] growth bodyRel
        have bodyRun : evaluateTuple ([body], values ++ env, middle) = (result, final) := by
          simpa [evaluateTuple] using run
        obtain ⟨targetFinal, targetBody, finalRel⟩ := bodyIH (values ++ env) middle final targetMiddle
          result middleRel bodyRel' bodyRun notTypeError
        change evaluate [body'] (values ++ env) targetMiddle = _ at targetBody
        exact ⟨targetFinal, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetBindings]; exact targetBody, finalRel⟩

/-- The Handle case of the inlining simulation, carrying a raised value to the
handler and transporting its relation across code growth. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_handle {C F : Type} (limit : Nat)
    (body handler body' handler' : Bvl.Exp) (env : List BvlSem.Value)
    (bodyIH : ∀ (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code [body] [body'] →
      evaluateTuple ([body], env, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple ([body'], env, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (handlerIH : ∀ (handlerEnv : List BvlSem.Value)
      (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code [handler] [handler'] →
      evaluateTuple ([handler], handlerEnv, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple ([handler'], handlerEnv, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (expressions : ExpRel source.code [.handle body handler] [.handle body' handler'])
    (run : evaluateTuple ([.handle body handler], env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.handle body' handler'], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  cases expressions with
  | handle bodyRel handlerRel =>
    simp only [evaluateTuple] at run
    rw [evaluate, fixClock_evaluate] at run
    cases bodyRun : evaluate [body] env source with
    | mk bodyResult middle =>
      rw [bodyRun] at run
      have bodyNotType : bodyResult ≠ .err (.abort .typeError) := by
        intro bad
        subst bodyResult
        simp at run
        exact notTypeError run.1.symm
      have bodyTuple : evaluateTuple ([body], env, source) = (bodyResult, middle) := bodyRun
      obtain ⟨targetMiddle, targetBody, middleRel⟩ :=
        bodyIH source middle target bodyResult related bodyRel bodyTuple bodyNotType
      change evaluate [body'] env target = _ at targetBody
      cases bodyResult with
      | val values =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨targetMiddle, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetBody], middleRel⟩
      | err error =>
        cases error with
        | abort reason =>
          simp at run
          rcases run with ⟨rfl, rfl⟩
          exact ⟨targetMiddle, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetBody], middleRel⟩
        | raise value =>
          have growth := evaluateMono [body] env source (.err (.raise value)) middle bodyTuple
          have handlerRel' := subsptExpRel source.code middle.code [handler] [handler'] growth handlerRel
          have handlerRun : evaluateTuple ([handler], value :: env, middle) = (result, final) := by
            simpa [evaluateTuple] using run
          obtain ⟨targetFinal, targetHandler, finalRel⟩ := handlerIH (value :: env) middle final targetMiddle
            result middleRel handlerRel' handlerRun notTypeError
          change evaluate [handler'] (value :: env) targetMiddle = _ at targetHandler
          exact ⟨targetFinal, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetBody]; exact targetHandler,
            finalRel⟩

/-- The If case of the inlining simulation, composing condition and selected
branch induction hypotheses after any source-code growth. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_if {C F : Type} (limit : Nat)
    (condition yes no condition' yes' no' : Bvl.Exp) (env : List BvlSem.Value)
    (conditionIH : ∀ (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code [condition] [condition'] →
      evaluateTuple ([condition], env, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple ([condition'], env, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (branchIH : ∀ (choice : Bool) (source final : State (Spt (Nat × Bvl.Exp) × C) F)
      (target : State C F) (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target →
      ExpRel source.code [if choice then yes else no] [if choice then yes' else no'] →
      evaluateTuple ([if choice then yes else no], env, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple ([if choice then yes' else no'], env, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (expressions : ExpRel source.code [.ifThenElse condition yes no] [.ifThenElse condition' yes' no'])
    (run : evaluateTuple ([.ifThenElse condition yes no], env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.ifThenElse condition' yes' no'], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  cases expressions with
  | ifThenElse conditionRel yesRel noRel =>
    simp only [evaluateTuple] at run
    rw [evaluate, fixClock_evaluate] at run
    cases conditionRun : evaluate [condition] env source with
    | mk conditionResult middle =>
      rw [conditionRun] at run
      have conditionNotType : conditionResult ≠ .err (.abort .typeError) := by
        cases conditionResult with
        | val values => simp
        | err error =>
          simp at run
          rcases run with ⟨rfl, _⟩
          exact notTypeError
      have conditionTuple : evaluateTuple ([condition], env, source) = (conditionResult, middle) := conditionRun
      obtain ⟨targetMiddle, targetCondition, middleRel⟩ :=
        conditionIH source middle target conditionResult related conditionRel conditionTuple conditionNotType
      change evaluate [condition'] env target = _ at targetCondition
      cases conditionResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨targetMiddle, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetCondition], middleRel⟩
      | val values =>
        obtain ⟨value, rfl⟩ := evaluate_singleton condition env source middle values conditionRun
        have growth := evaluateMono [condition] env source (.val [value]) middle conditionTuple
        cases boolRun : asBool value with
        | none =>
          simp [boolRun] at run
          exact (notTypeError run.1.symm).elim
        | some choice =>
          cases choice with
          | false =>
            simp [boolRun] at run
            have branchRel := subsptExpRel source.code middle.code [no] [no'] growth noRel
            obtain ⟨targetFinal, targetBranch, finalRel⟩ := branchIH false middle final targetMiddle result
              middleRel branchRel (by simpa [evaluateTuple] using run) notTypeError
            change evaluate [no'] env targetMiddle = _ at targetBranch
            refine ⟨targetFinal, ?_, finalRel⟩
            rw [evaluateTuple, evaluate, fixClock_evaluate, targetCondition]
            simpa [boolRun] using targetBranch
          | true =>
            simp [boolRun] at run
            have branchRel := subsptExpRel source.code middle.code [yes] [yes'] growth yesRel
            obtain ⟨targetFinal, targetBranch, finalRel⟩ := branchIH true middle final targetMiddle result
              middleRel branchRel (by simpa [evaluateTuple] using run) notTypeError
            change evaluate [yes'] env targetMiddle = _ at targetBranch
            refine ⟨targetFinal, ?_, finalRel⟩
            rw [evaluateTuple, evaluate, fixClock_evaluate, targetCondition]
            simpa [boolRun] using targetBranch

/-- The operator case of the inlining simulation, including installation. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "evaluate_inline"
  (fmap_as_finite_support := [refs])]
theorem evaluateInline_op {C F : Type} (limit : Nat)
    (op : ClosLang.Op) (args args' : List Bvl.Exp) (env : List BvlSem.Value)
    (argsIH : ∀ (source final : State (Spt (Nat × Bvl.Exp) × C) F) (target : State C F)
      (result : Result (List BvlSem.Value) BvlSem.Value),
      inStateRel limit source target → ExpRel source.code args args' →
      evaluateTuple (args, env, source) = (result, final) →
      result ≠ .err (.abort .typeError) →
      ∃ targetFinal, evaluateTuple (args', env, target) = (result, targetFinal) ∧
        inStateRel limit final targetFinal)
    (source final : Flapjack.Compiler.Backend.BvlSem.State (Spt (Nat × Bvl.Exp) × C) F)
    (target : Flapjack.Compiler.Backend.BvlSem.State C F)
    (result : Result (List BvlSem.Value) BvlSem.Value)
    (related : inStateRel limit source target)
    (expressions : ExpRel source.code [.op op args] [.op op args'])
    (run : evaluateTuple ([.op op args], env, source) = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    ∃ targetFinal, evaluateTuple ([.op op args'], env, target) = (result, targetFinal) ∧
      inStateRel limit final targetFinal := by
  cases expressions with
  | op argsRel =>
    simp only [evaluateTuple] at run
    rw [evaluate, fixClock_evaluate] at run
    cases argsRun : evaluate args env source with
    | mk argsResult middle =>
      rw [argsRun] at run
      have argsNotType : argsResult ≠ .err (.abort .typeError) := by
        cases argsResult with
        | val values => simp
        | err error =>
          simp at run
          rcases run with ⟨rfl, _⟩
          exact notTypeError
      obtain ⟨targetMiddle, targetArgs, middleRel⟩ := argsIH source middle target argsResult
        related argsRel (by simpa [evaluateTuple] using argsRun) argsNotType
      change evaluate args' env target = _ at targetArgs
      cases argsResult with
      | err error =>
        simp at run
        rcases run with ⟨rfl, rfl⟩
        exact ⟨targetMiddle, by rw [evaluateTuple, evaluate, fixClock_evaluate, targetArgs], middleRel⟩
      | val values =>
        have simulated := inDoApp limit middle targetMiddle middleRel op values.reverse
        cases appRun : doApp op values.reverse middle with
        | err error =>
          simp [appRun] at run simulated
          rcases run with ⟨rfl, rfl⟩
          have appNotType : error ≠ .abort .typeError := by
            intro equal
            subst error
            exact notTypeError rfl
          have targetApp := simulated appNotType
          refine ⟨targetMiddle, ?_, middleRel⟩
          rw [evaluateTuple, evaluate, fixClock_evaluate, targetArgs]
          simp [targetApp]
        | val pair =>
          obtain ⟨value, next⟩ := pair
          simp [appRun] at run simulated
          rcases run with ⟨rfl, rfl⟩
          obtain ⟨targetFinal, finalRel, targetApp⟩ := simulated
          refine ⟨targetFinal, ?_, finalRel⟩
          rw [evaluateTuple, evaluate, fixClock_evaluate, targetArgs]
          simp [targetApp]

end Flapjack.Compiler.Backend.BvlInline.Proofs

module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateAppExpression
public import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateInstall

@[expose] public section

/-! Clock and expression-weight induction for multi-argument introduction. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- Application simulation at or below a source clock bound. -/
def ApplicationRelWithin {C F : Type} (limit : Nat) : Prop :=
  ∀ (source target : State C F) (sourceFunction targetFunction : Value)
    (sourceArgs targetArgs : List Value), source.clock ≤ limit → StateRel source target →
    ValueRel source.maxApp sourceFunction targetFunction →
    List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs → sourceArgs.length ≤ source.maxApp →
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluateApps sourceFunction sourceArgs source).1 (evaluateApp none targetFunction targetArgs target).1 ∧
    StateRel (evaluateApps sourceFunction sourceArgs source).2
      (evaluateApp none targetFunction targetArgs target).2

/-- Lean-side evaluator simulation by simultaneous clock and target-expression
weight induction. HOL evaluator correspondence remains a separate obligation. -/
theorem evaluate_mutual_within {C F : Type} (limit : Nat) :
    ApplicationRelWithin (C := C) (F := F) limit ∧
      ∀ sourceCode targetCode, EvaluateRelWithin (C := C) (F := F) limit sourceCode targetCode := by
  induction limit using Nat.strongRecOn with
  | ind limit clockIH =>
    have appAll : ApplicationRelWithin (C := C) (F := F) limit := by
      intro source target sourceFunction targetFunction sourceArgs targetArgs clock states functions args bound
      by_cases smaller : source.clock < limit
      · exact (clockIH source.clock smaller).1 source target sourceFunction targetFunction sourceArgs targetArgs
          (by omega) states functions args bound
      · apply evaluateApp_value_related source target sourceFunction targetFunction sourceArgs targetArgs
          states functions args bound
        · intro sourceBody targetBody targetEnv target sourceEnv targetFinal source targetResult bodyClock
          exact (clockIH source.clock (by omega)).2 [sourceBody] [targetBody]
            targetEnv target sourceEnv targetFinal source targetResult (by omega)
        · intro nextSource nextTarget sourceValue targetValue sourceValues targetValues appClock
          exact (clockIH nextSource.clock (by omega)).1 nextSource nextTarget sourceValue targetValue
            sourceValues targetValues (by omega)
    constructor
    · exact appAll
    · intro sourceCode targetCode
      have allWeights : ∀ weight targetCode, expsWeight targetCode = weight →
          ∀ sourceCode, EvaluateRelWithin (C := C) (F := F) limit sourceCode targetCode := by
        intro weight
        induction weight using Nat.strongRecOn with
        | ind weight weightIH =>
          intro targetCode measure sourceCode
          have structural : ∀ targetCode, expsWeight targetCode < weight →
              ∀ sourceCode, EvaluateRelWithin (C := C) (F := F) limit sourceCode targetCode := by
            intro targetCode smaller sourceCode
            exact weightIH (expsWeight targetCode) smaller targetCode rfl sourceCode
          cases targetCode with
          | nil => exact evaluateRelAt_within limit sourceCode [] (evaluateRel_nil sourceCode)
          | cons first rest =>
            cases rest with
            | cons second tail =>
              apply evaluateRel_consWithin limit first second tail
              · intro code
                apply structural [first] (by simp only [expsWeight] at measure ⊢; omega)
              · intro code
                apply structural (second :: tail) (by simp only [expsWeight] at measure ⊢; omega)
            | nil =>
              cases first with
              | var trace index => exact evaluateRelAt_within limit sourceCode _ (evaluateRel_var sourceCode trace index)
              | fn name location vars arity body =>
                exact evaluateRelAt_within limit sourceCode _ (evaluateRel_fn name location vars arity body sourceCode)
              | call trace ticks location args =>
                exact evaluateRelAt_within limit sourceCode _ (evaluateRel_call sourceCode trace ticks location args)
              | tick trace body =>
                apply evaluateRel_tickWithin limit trace body
                intro code
                apply structural [body] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              | raise trace body =>
                apply evaluateRel_raiseWithin limit trace body
                intro code
                apply structural [body] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              | «let» trace bindings body =>
                apply evaluateRel_letWithin limit trace bindings body
                · intro code
                  apply structural bindings (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                · intro code
                  apply structural [body] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              | letrec names location vars functions body =>
                apply evaluateRel_letrecWithin limit names location vars functions body
                intro code
                apply structural [body] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              | handle trace body handler =>
                apply evaluateRel_handleWithin limit trace body handler
                · intro code
                  apply structural [body] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                · intro code
                  apply structural [handler] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              | ifThenElse trace condition yes no =>
                apply evaluateRel_ifWithin limit trace condition yes no
                · intro code
                  apply structural [condition] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                · intro code
                  apply structural [yes] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                · intro code
                  apply structural [no] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
              | app trace location head args =>
                intro targetEnv target sourceEnv targetFinal source targetResult sourceClock
                apply evaluateRel_app limit trace location head args sourceCode
                · intro code
                  apply structural args (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                · intro code
                  apply structural [head] (by simp only [expsWeight, expWeight] at measure ⊢; omega)
                · exact sourceClock
                · intro sourceBody targetBody targetEnv target sourceEnv targetFinal source targetResult smaller
                  exact (clockIH source.clock smaller).2 [sourceBody] [targetBody]
                    targetEnv target sourceEnv targetFinal source targetResult (by omega)
                · intro s t sv tv sa ta smaller
                  exact (clockIH s.clock smaller).1 s t sv tv sa ta (by omega)
              | op trace op args =>
                have argsIH : ∀ code, EvaluateRelWithin (C := C) (F := F) limit code args := by
                  intro code
                  apply structural args
                  have smaller := opWeight_gt trace op args
                  simp only [expsWeight] at measure
                  omega
                by_cases install : op = .install
                · subst op
                  intro targetEnv target sourceEnv targetFinal source targetResult sourceClock run env states code
                  apply evaluateRel_installWithin limit trace args sourceCode argsIH targetEnv target sourceEnv
                    targetFinal source targetResult sourceClock
                  · intro targetProgram installedTarget targetSmaller sourceProgram installedSource
                      installedResult installedFinal installedRun installedStates installedCode
                    have initialClocks := (stateRel_clock_maxApp states).1
                    have installedClocks := (stateRel_clock_maxApp installedStates).1
                    have smaller : installedSource.clock < limit := by omega
                    exact (clockIH installedSource.clock smaller).2 sourceProgram targetProgram
                      [] installedTarget [] installedFinal installedSource installedResult (by omega)
                      installedRun .nil installedStates installedCode
                  · exact run
                  · exact env
                  · exact states
                  · exact code
                · by_cases force : op = .thunkOp .forceThunk
                  · subst op
                    apply evaluateRel_forceWithin limit trace args sourceCode argsIH
                    intro code
                    apply structural [appUnit (.var .none 0)]
                    simp only [expsWeight, expWeight, appUnit] at measure ⊢
                    omega
                  · exact evaluateRel_allOrdinaryWithin limit trace op args sourceCode install force argsIH

      exact allWeights (expsWeight targetCode) targetCode rfl sourceCode

namespace IntroMultiWitness
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ state : StateBroad C F, (State.ofBroad state).toBroad = state) ∧
      (∀ state : State C F, State.ofBroad state.toBroad = state) :=
  ClosSem.holFmapAsFiniteSupportWitness
end IntroMultiWitness

/-- The mutual expression and application simulations for multi-argument
introduction, with the original target evaluation and relation premises. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "evaluate_intro_multi"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_intro_multi {C F : Type} :
    (∀ (targetCode : List ClosLang.Exp) (targetEnv : List Value) (target : State C F)
      (sourceEnv : List Value) (targetFinal source : State C F)
      (targetResult : SemanticPrimitivesHOL.Result (List Value) Value) (sourceCode : List ClosLang.Exp),
      evaluate targetCode targetEnv target = (targetResult, targetFinal) ∧
      List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv ∧ StateRel source target ∧
      CodeRel source.maxApp sourceCode targetCode →
      ∃ sourceResult sourceFinal,
        evaluate sourceCode sourceEnv source = (sourceResult, sourceFinal) ∧
        resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
          sourceResult targetResult ∧ StateRel sourceFinal targetFinal) ∧
    (∀ (location : Option Nat) (targetFunction : Value) (targetArgs : List Value) (target : State C F)
      (targetResult : SemanticPrimitivesHOL.Result (List Value) Value) (targetFinal : State C F)
      (sourceFunction : Value) (sourceArgs : List Value) (source : State C F),
      evaluateApp location targetFunction targetArgs target = (targetResult, targetFinal) ∧
      location = none ∧ ValueRel source.maxApp sourceFunction targetFunction ∧
      List.Forall₂ (ValueRel source.maxApp) sourceArgs targetArgs ∧ StateRel source target ∧
      sourceArgs.length ≤ source.maxApp →
      ∃ sourceResult sourceFinal,
        evaluateApps sourceFunction sourceArgs source = (sourceResult, sourceFinal) ∧
        resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
          sourceResult targetResult ∧ StateRel sourceFinal targetFinal) := by
  constructor
  · intro targetCode targetEnv target sourceEnv targetFinal source targetResult sourceCode premises
    obtain ⟨run, envRel, states, codeRel⟩ := premises
    exact (evaluate_mutual_within (C := C) (F := F) source.clock).2 sourceCode targetCode
      targetEnv target sourceEnv targetFinal source targetResult (by omega) run envRel states codeRel
  · intro location targetFunction targetArgs target targetResult targetFinal sourceFunction sourceArgs source premises
    obtain ⟨run, locationEq, functions, args, states, bound⟩ := premises
    subst location
    have related := (evaluate_mutual_within (C := C) (F := F) source.clock).1
      source target sourceFunction targetFunction sourceArgs targetArgs (by omega) states functions args bound
    rw [run] at related
    exact ⟨(evaluateApps sourceFunction sourceArgs source).1,
      (evaluateApps sourceFunction sourceArgs source).2, (Prod.eta _).symm, related.1, related.2⟩

/-- Forward correctness of multi-argument introduction. The independent
unused binder is present in the typed HOL statement. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "intro_multi_correct"
  (fmap_as_finite_support := [refs, code])]
theorem intro_multi_correct {C F A : Type} [Nonempty A] (sourceCode : List ClosLang.Exp)
    (sourceEnv : List Value) (source : State C F)
    (sourceResult : SemanticPrimitivesHOL.Result (List Value) Value)
    (sourceFinal : State C F) (targetEnv : List Value) (_unused : A) (target : State C F)
    (premises : evaluate sourceCode sourceEnv source = (sourceResult, sourceFinal) ∧
      (∀ expression ∈ sourceCode, ClosProps.noMti expression) ∧
      List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv ∧ StateRel source target) :
    ∃ targetResult targetFinal,
      evaluate (introList source.maxApp sourceCode) targetEnv target = (targetResult, targetFinal) ∧
      resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
        sourceResult targetResult ∧ StateRel sourceFinal targetFinal := by
  obtain ⟨sourceRun, unary, envRel, states⟩ := premises
  cases targetRun : evaluate (introList source.maxApp sourceCode) targetEnv target with
  | mk targetResult targetFinal =>
    obtain ⟨relatedResult, relatedFinal, relatedRun, resultRel, finalStates⟩ :=
      (evaluate_intro_multi (C := C) (F := F)).1 (introList source.maxApp sourceCode)
        targetEnv target sourceEnv targetFinal source targetResult sourceCode
        ⟨targetRun, envRel, states, unary, rfl⟩
    rw [sourceRun] at relatedRun
    cases relatedRun
    exact ⟨targetResult, targetFinal, rfl, resultRel, finalStates⟩

end Flapjack.Compiler.Backend.ClosMti

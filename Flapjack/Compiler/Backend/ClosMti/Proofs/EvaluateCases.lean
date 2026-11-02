import Flapjack.Compiler.Backend.ClosMti.Proofs.Applications
import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallConst
import Flapjack.SemanticPrimitivesProps.ResultRelation

/-! Base cases of the multi-argument introduction evaluation simulation. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- The expression half of the backward simulation, specialized to a pair of
programs. The evaluator remains under source correspondence review. -/
def EvaluateRelAt {C F : Type} (sourceCode targetCode : List ClosLang.Exp) : Prop :=
  ∀ (targetEnv : List Value) (target : State C F) (sourceEnv : List Value)
    (targetFinal : State C F) (source : State C F)
    (targetResult : SemanticPrimitivesHOL.Result (List Value) Value),
    evaluate targetCode targetEnv target = (targetResult, targetFinal) →
    List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv →
    StateRel source target → CodeRel source.maxApp sourceCode targetCode →
    ∃ sourceResult sourceFinal,
      evaluate sourceCode sourceEnv source = (sourceResult, sourceFinal) ∧
      resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
        sourceResult targetResult ∧ StateRel sourceFinal targetFinal

/-- A unary source expression can transform into a variable only if it was
the same variable. -/
theorem introExp_eq_var (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (index : Nat) (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .var trace index) : expression = .var trace index := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Empty target code is simulated by empty source code. -/
theorem evaluateRel_nil {C F : Type} (sourceCode : List ClosLang.Exp) :
    @EvaluateRelAt C F sourceCode [] := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  have sourceEmpty : sourceCode = [] := List.eq_nil_of_length_eq_zero (by simpa using length.symm)
  subst sourceCode
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨.val [], source, by rw [evaluate], by simp [resultRel], states⟩

/-- Pointwise lookup preserves a list relation, including out-of-range indices. -/
theorem forall₂_getElemRel {A B : Type} {rel : A → B → Prop} {left : List A} {right : List B}
    (related : List.Forall₂ rel left right) (index : Nat) :
    OptionRel rel left[index]? right[index]? := by
  induction related generalizing index with
  | nil => cases index <;> trivial
  | cons head tail ih => cases index <;> simp_all [OptionRel]

/-- The variable case of the backward evaluation simulation. -/
theorem evaluateRel_var {C F : Type} (sourceCode : List ClosLang.Exp)
    (trace : BackendCommon.Tra) (index : Nat) :
    @EvaluateRelAt C F sourceCode [.var trace index] := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .var trace index := by
        simpa [introList] using code.2.symm
      have same := introExp_eq_var source.maxApp expression trace index unary transformed
      subst expression
      have lookups := forall₂_getElemRel env index
      cases sourceLookup : sourceEnv[index]? with
      | none =>
        cases targetLookup : targetEnv[index]? with
        | none =>
          simp [evaluate, targetLookup] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨.err (.abort .typeError), source, by simp [evaluate, sourceLookup],
            by simp [resultRel, excRel], states⟩
        | some value => simp [OptionRel, sourceLookup, targetLookup] at lookups
      | some value =>
        cases targetLookup : targetEnv[index]? with
        | none => simp [OptionRel, sourceLookup, targetLookup] at lookups
        | some targetValue =>
          simp [OptionRel, sourceLookup, targetLookup] at lookups
          simp [evaluate, targetLookup] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨.val [value], source, by simp [evaluate, sourceLookup],
            by simpa [resultRel] using List.Forall₂.cons lookups List.Forall₂.nil, states⟩

/-- The multi-expression case composes the simulations for the first
expression and the remaining list. -/
theorem evaluateRel_cons {C F : Type} (targetHead targetSecond : ClosLang.Exp)
    (targetTail : List ClosLang.Exp)
    (headIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode [targetHead])
    (tailIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode (targetSecond :: targetTail))
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelAt C F sourceCode (targetHead :: targetSecond :: targetTail) := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons sourceHead sourceRest =>
    cases sourceRest with
    | nil => simp at length
    | cons sourceSecond sourceTail =>
      have parts := (codeRel_cons sourceHead targetHead (sourceSecond :: sourceTail)
        (targetSecond :: targetTail)).mp code
      cases targetHeadRun : evaluate [targetHead] targetEnv target with
      | mk headResult targetMiddle =>
        obtain ⟨sourceHeadResult, sourceMiddle, sourceHeadRun, headRel, middleStates⟩ :=
          headIH [sourceHead] targetEnv target sourceEnv targetMiddle source headResult
            targetHeadRun env states parts.1
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 [sourceHead] sourceEnv source
          simpa [sourceHeadRun] using preserved
        have envMiddle : List.Forall₂ (ValueRel sourceMiddle.maxApp) sourceEnv targetEnv := by
          simpa [maxEq] using env
        have tailCode : CodeRel sourceMiddle.maxApp (sourceSecond :: sourceTail)
            (targetSecond :: targetTail) := by simpa [maxEq] using parts.2
        cases headResult with
        | err targetError =>
          cases sourceHeadResult with
          | val values => simp [resultRel] at headRel
          | err sourceError =>
            rw [evaluate, fixClock_evaluate, targetHeadRun] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            refine ⟨.err sourceError, sourceMiddle, ?_, headRel, middleStates⟩
            rw [evaluate, fixClock_evaluate, sourceHeadRun]
        | val targetValues =>
          cases sourceHeadResult with
          | err sourceError => simp [resultRel] at headRel
          | val sourceValues =>
            have targetLength := evaluate_length.1 [targetHead] targetEnv target targetMiddle
              targetValues targetHeadRun
            have sourceLength := evaluate_length.1 [sourceHead] sourceEnv source sourceMiddle
              sourceValues sourceHeadRun
            cases targetValues with
            | nil => simp at targetLength
            | cons targetValue targetExtra =>
              cases targetExtra with
              | cons value tail => simp at targetLength
              | nil =>
                cases sourceValues with
                | nil => simp at sourceLength
                | cons sourceValue sourceExtra =>
                  cases sourceExtra with
                  | cons value tail => simp at sourceLength
                  | nil =>
                    have valuesRel : ValueRel source.maxApp sourceValue targetValue := by
                      simpa [resultRel] using headRel
                    cases targetTailRun : evaluate (targetSecond :: targetTail) targetEnv targetMiddle with
                    | mk targetTailResult targetLast =>
                      obtain ⟨sourceTailResult, sourceFinal, sourceTailRun, tailRel, finalStates⟩ :=
                        tailIH (sourceSecond :: sourceTail) targetEnv targetMiddle sourceEnv targetLast
                          sourceMiddle targetTailResult targetTailRun envMiddle middleStates tailCode
                      cases targetTailResult with
                      | err targetError =>
                        rw [evaluate, fixClock_evaluate, targetHeadRun, targetTailRun] at run
                        simp only [Prod.mk.injEq] at run
                        obtain ⟨rfl, rfl⟩ := run
                        cases sourceTailResult with
                        | val values => simp [resultRel] at tailRel
                        | err sourceError =>
                          refine ⟨.err sourceError, sourceFinal, ?_, ?_, finalStates⟩
                          · rw [evaluate, fixClock_evaluate, sourceHeadRun, sourceTailRun]
                          · simpa [resultRel, maxEq] using tailRel
                      | val targetValues =>
                        rw [evaluate, fixClock_evaluate, targetHeadRun, targetTailRun] at run
                        simp only [Prod.mk.injEq] at run
                        obtain ⟨rfl, rfl⟩ := run
                        cases sourceTailResult with
                        | err sourceError => simp [resultRel] at tailRel
                        | val sourceValues =>
                          refine ⟨.val (sourceValue :: sourceValues), sourceFinal, ?_, ?_, finalStates⟩
                          · rw [evaluate, fixClock_evaluate, sourceHeadRun, sourceTailRun]
                            rfl
                          · have restRel : List.Forall₂ (ValueRel source.maxApp) sourceValues targetValues := by
                              simpa [resultRel, maxEq] using tailRel
                            simpa [resultRel] using List.Forall₂.cons valuesRel restRel

end Flapjack.Compiler.Backend.ClosMti

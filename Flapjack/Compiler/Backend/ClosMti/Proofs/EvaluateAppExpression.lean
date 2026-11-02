import Flapjack.Compiler.Backend.ClosMti.Proofs.EvaluateRecursiveApplication

/-! Evaluation of collected application expressions. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack ClosSem SemanticPrimitivesProps

/-- A transformed application comes from an unannotated unary source
application, with head and argument list produced by the collector. -/
theorem introExp_eq_app (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (location : Option Nat) (targetHead : ClosLang.Exp) (targetArgs : List ClosLang.Exp)
    (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .app trace location targetHead targetArgs) :
    ∃ head arg collectedArgs collectedHead,
      expression = .app trace none head [arg] ∧ location = none ∧
      collectApps maxApp [arg] head = (collectedArgs, collectedHead) ∧
      targetHead = introExp maxApp collectedHead ∧ targetArgs = introList maxApp collectedArgs := by
  cases expression
  case app sourceTrace sourceLocation sourceHead sourceArgs =>
    simp only [ClosProps.noMti] at unary
    obtain ⟨arity, rfl, _, _⟩ := unary
    cases sourceArgs with
    | nil => simp at arity
    | cons arg rest =>
      cases rest with
      | cons next tail => simp at arity
      | nil =>
        cases found : collectApps maxApp [arg] sourceHead with
        | mk args head =>
          simp only [introExp_app_none, found] at transformed
          simp only [ClosLang.Exp.app.injEq] at transformed
          obtain ⟨rfl, rfl, headEq, argsEq⟩ := transformed
          exact ⟨sourceHead, arg, args, head, rfl, rfl, found, headEq.symm, argsEq.symm⟩
  all_goals simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
    introExp_handle, introExp_tick, introExp_op, introExp_fn_none, introExp_letrec_none]

/-- A collected application simulates its reconstructed unary applications,
assuming simulations for the collected arguments, head, and value application.
The latter is available at the same clock; the enclosing mutual induction and
the correspondence of this evaluator to HOL remain open. -/
theorem evaluate_collected_app_related {C F : Type} (source target : State C F)
    (sourceEnv targetEnv : List Value) (sourceArgs targetArgs : List ClosLang.Exp)
    (sourceHead targetHead : ClosLang.Exp) (traces : List BackendCommon.Tra) (trace : BackendCommon.Tra)
    (states : StateRel source target)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (argsCode : CodeRel source.maxApp sourceArgs targetArgs)
    (headCode : CodeRel source.maxApp [sourceHead] [targetHead])
    (lengthEq : sourceArgs.length = traces.length) (bound : sourceArgs.length ≤ source.maxApp)
    (nonempty : targetArgs ≠ [])
    (argsIH : EvaluateRelAt (C := C) (F := F) sourceArgs targetArgs)
    (headIH : EvaluateRelAt (C := C) (F := F) [sourceHead] [targetHead])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock ≤ source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluate [mkApps sourceHead (traces.zip sourceArgs)] sourceEnv source).1
      (evaluate [.app trace none targetHead targetArgs] targetEnv target).1 ∧
    StateRel
      (evaluate [mkApps sourceHead (traces.zip sourceArgs)] sourceEnv source).2
      (evaluate [.app trace none targetHead targetArgs] targetEnv target).2 := by
  have targetArgsNonempty : targetArgs.isEmpty = false := by
    cases targetArgs with
    | nil => exact (nonempty rfl).elim
    | cons head tail => rfl
  cases targetArgsRun : evaluate targetArgs targetEnv target with
  | mk targetArgsResult targetMiddle =>
    obtain ⟨sourceArgsResult, sourceMiddle, sourceArgsRun, argsRelated, middleStates⟩ :=
      argsIH targetEnv target sourceEnv targetMiddle source targetArgsResult targetArgsRun envRel states argsCode
    have middleMax : sourceMiddle.maxApp = source.maxApp := by
      have invariant := ClosProps.evaluate_const.1 sourceArgs sourceEnv source
      simpa [sourceArgsRun] using invariant
    have middleClock : sourceMiddle.clock ≤ source.clock := by
      have invariant := evaluate_clock_le sourceArgs sourceEnv source
      simpa [sourceArgsRun] using invariant
    cases targetArgsResult with
    | err targetError =>
      cases sourceArgsResult with
      | val values => simp [resultRel] at argsRelated
      | err sourceError =>
        have sourceRun := mkApps_argument_error traces sourceArgs sourceEnv source sourceMiddle
          sourceError sourceHead sourceArgsRun lengthEq
        rw [sourceRun, evaluate, fixClock_evaluate, targetArgsRun]
        simp [nonempty, argsRelated, middleStates]
    | val targetValues =>
      cases sourceArgsResult with
      | err error => simp [resultRel] at argsRelated
      | val sourceValues =>
        cases targetHeadRun : evaluate [targetHead] targetEnv targetMiddle with
        | mk targetHeadResult targetLast =>
          obtain ⟨sourceHeadResult, sourceLast, sourceHeadRun, headRelated, lastStates⟩ :=
            headIH targetEnv targetMiddle sourceEnv targetLast sourceMiddle targetHeadResult targetHeadRun
              (by simpa [middleMax] using envRel) middleStates (by simpa [middleMax] using headCode)
          have lastMax : sourceLast.maxApp = source.maxApp := by
            have invariant := ClosProps.evaluate_const.1 [sourceHead] sourceEnv sourceMiddle
            have last : sourceLast.maxApp = sourceMiddle.maxApp := by simpa [sourceHeadRun] using invariant
            omega
          have lastClock : sourceLast.clock ≤ source.clock := by
            have invariant := evaluate_clock_le [sourceHead] sourceEnv sourceMiddle
            have last : sourceLast.clock ≤ sourceMiddle.clock := by simpa [sourceHeadRun] using invariant
            omega
          cases targetHeadResult with
          | err targetError =>
            cases sourceHeadResult with
            | val values => simp [resultRel] at headRelated
            | err sourceError =>
              have sourceRun := mkApps_function_error traces sourceArgs sourceEnv source sourceMiddle
                sourceLast sourceValues sourceError sourceHead sourceHeadRun sourceArgsRun lengthEq
              rw [sourceRun, evaluate, fixClock_evaluate, targetArgsRun]
              simp only [targetArgsNonempty, Bool.false_eq_true, ↓reduceIte]
              rw [fixClock_evaluate, targetHeadRun]
              simpa [nonempty, middleMax] using And.intro headRelated lastStates
          | val targetFunctions =>
            obtain ⟨targetFunction, rfl⟩ := evaluate_singleton_value targetHead targetEnv targetMiddle
              targetLast targetFunctions targetHeadRun
            cases sourceHeadResult with
            | err error => simp [resultRel] at headRelated
            | val sourceFunctions =>
              obtain ⟨sourceFunction, rfl⟩ := evaluate_singleton_value sourceHead sourceEnv sourceMiddle
                sourceLast sourceFunctions sourceHeadRun
              have valuesRel : List.Forall₂ (ValueRel sourceLast.maxApp) sourceValues targetValues := by
                simpa [resultRel, lastMax] using argsRelated
              have functionRel : ValueRel sourceLast.maxApp sourceFunction targetFunction := by
                simpa [resultRel, middleMax, lastMax] using headRelated
              have valuesBound : sourceValues.length ≤ sourceLast.maxApp := by
                have lengths := evaluate_length.1 sourceArgs sourceEnv source sourceMiddle sourceValues sourceArgsRun
                omega
              have applied := appIH sourceLast targetLast sourceFunction targetFunction sourceValues targetValues
                lastClock lastStates functionRel valuesRel valuesBound
              have sourceRun := mkApps_success traces sourceArgs sourceEnv source sourceMiddle sourceLast
                sourceValues sourceFunction sourceHead sourceHeadRun sourceArgsRun lengthEq
              rw [sourceRun, evaluate, fixClock_evaluate, targetArgsRun]
              simp only [targetArgsNonempty, Bool.false_eq_true, ↓reduceIte]
              rw [fixClock_evaluate, targetHeadRun]
              simpa [nonempty, lastMax] using applied

/-- The collected-expression case follows from the structural hypotheses for
its arguments and head and the two smaller-clock evaluator hypotheses. -/
theorem evaluate_collected_app_step {C F : Type} (source target : State C F)
    (sourceEnv targetEnv : List Value) (sourceArgs targetArgs : List ClosLang.Exp)
    (sourceHead targetHead : ClosLang.Exp) (traces : List BackendCommon.Tra) (trace : BackendCommon.Tra)
    (states : StateRel source target)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (argsCode : CodeRel source.maxApp sourceArgs targetArgs)
    (headCode : CodeRel source.maxApp [sourceHead] [targetHead])
    (lengthEq : sourceArgs.length = traces.length) (bound : sourceArgs.length ≤ source.maxApp)
    (nonempty : targetArgs ≠ [])
    (argsIH : EvaluateRelAt (C := C) (F := F) sourceArgs targetArgs)
    (headIH : EvaluateRelAt (C := C) (F := F) [sourceHead] [targetHead])
    (bodyIH : ∀ sourceBody targetBody,
      EvaluateRelBelow (C := C) (F := F) source.clock [sourceBody] [targetBody])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock < source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluate [mkApps sourceHead (traces.zip sourceArgs)] sourceEnv source).1
      (evaluate [.app trace none targetHead targetArgs] targetEnv target).1 ∧
    StateRel
      (evaluate [mkApps sourceHead (traces.zip sourceArgs)] sourceEnv source).2
      (evaluate [.app trace none targetHead targetArgs] targetEnv target).2 := by
  apply evaluate_collected_app_related source target sourceEnv targetEnv sourceArgs targetArgs
    sourceHead targetHead traces trace states envRel argsCode headCode lengthEq bound nonempty argsIH headIH
  intro s t sv tv sa ta clock related values arguments argsBound
  apply evaluateApp_value_related s t sv tv sa ta related values arguments argsBound
  · intro sourceBody targetBody targetEnv target sourceEnv targetFinal source targetResult smaller
    exact bodyIH sourceBody targetBody targetEnv target sourceEnv targetFinal source targetResult (by omega)
  · intro nextSource nextTarget sourceValue targetValue sourceValues targetValues smaller
    exact appIH nextSource nextTarget sourceValue targetValue sourceValues targetValues (by omega)

/-- The unannotated unary application case of the multi-argument pass. The
collector supplies the reconstructed source expression, its argument bound,
and the unary invariants used by the structural induction hypotheses. -/
theorem evaluate_introApp_step {C F : Type} (source target : State C F)
    (sourceEnv targetEnv : List Value) (trace : BackendCommon.Tra)
    (head arg : ClosLang.Exp) (collectedArgs : List ClosLang.Exp) (collectedHead : ClosLang.Exp)
    (states : StateRel source target)
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (safe : ClosProps.noMti (.app trace none head [arg]))
    (collected : collectApps source.maxApp [arg] head = (collectedArgs, collectedHead))
    (argsIH : EvaluateRelAt (C := C) (F := F) collectedArgs (introList source.maxApp collectedArgs))
    (headIH : EvaluateRelAt (C := C) (F := F) [collectedHead] [introExp source.maxApp collectedHead])
    (bodyIH : ∀ sourceBody targetBody,
      EvaluateRelBelow (C := C) (F := F) source.clock [sourceBody] [targetBody])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock < source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2) :
    resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
      (evaluate [.app trace none head [arg]] sourceEnv source).1
      (evaluate [introExp source.maxApp (.app trace none head [arg])] targetEnv target).1 ∧
    StateRel
      (evaluate [.app trace none head [arg]] sourceEnv source).2
      (evaluate [introExp source.maxApp (.app trace none head [arg])] targetEnv target).2 := by
  have positive : 1 ≤ source.maxApp := by
    have agreement := stateRel_clock_maxApp states
    omega
  have outerCollected : collectApps source.maxApp [] (.app trace none head [arg]) =
      (collectedArgs, collectedHead) := by
    simpa [collectApps, positive] using collected
  obtain ⟨traces, rebuilt, lengths, bound⟩ :=
    collectAppsRebuild (.app trace none head [arg]) source.maxApp [] collectedArgs collectedHead
      outerCollected safe
  obtain ⟨argsSafe, headSafe⟩ := collectAppsNoMti source.maxApp [] (.app trace none head [arg])
    collectedArgs collectedHead outerCollected safe (by simp)
  have argsCode : CodeRel source.maxApp collectedArgs (introList source.maxApp collectedArgs) :=
    ⟨argsSafe, rfl⟩
  have headCode : CodeRel source.maxApp [collectedHead] [introExp source.maxApp collectedHead] := by
    simp [CodeRel, introList, headSafe]
  have argsNonempty : collectedArgs ≠ [] := by
    obtain ⟨suffix, prefixEq⟩ := collectAppsPrefix source.maxApp [arg] head collectedArgs collectedHead collected
    rw [prefixEq]
    simp
  have targetNonempty : introList source.maxApp collectedArgs ≠ [] := by
    intro empty
    have lengths := introList_length source.maxApp collectedArgs
    rw [empty] at lengths
    cases collectedArgs with
    | nil => exact argsNonempty rfl
    | cons first rest => simp at lengths
  have result := evaluate_collected_app_step source target sourceEnv targetEnv collectedArgs
    (introList source.maxApp collectedArgs) collectedHead (introExp source.maxApp collectedHead)
    traces trace states envRel argsCode headCode lengths bound targetNonempty argsIH headIH bodyIH appIH
  have targetEq : introExp source.maxApp (.app trace none head [arg]) =
      .app trace none (introExp source.maxApp collectedHead) (introList source.maxApp collectedArgs) := by
    simp [introExp_app_none, collected]
  rw [targetEq, rebuilt]
  exact result

/-- Target-driven application-expression simulation, with structural
hypotheses for the target head and arguments and smaller-clock hypotheses
for body evaluation and application. The enclosing induction remains open. -/
theorem evaluateRel_app {C F : Type} (trace : BackendCommon.Tra) (location : Option Nat)
    (targetHead : ClosLang.Exp) (targetArgs sourceCode : List ClosLang.Exp)
    (argsIH : ∀ sourceArgs, EvaluateRelAt (C := C) (F := F) sourceArgs targetArgs)
    (headIH : ∀ sourceHead, EvaluateRelAt (C := C) (F := F) [sourceHead] [targetHead])
    (targetEnv : List Value) (target : State C F) (sourceEnv : List Value)
    (targetFinal source : State C F) (targetResult : SemanticPrimitivesHOL.Result (List Value) Value)
    (bodyIH : ∀ sourceBody targetBody,
      EvaluateRelBelow (C := C) (F := F) source.clock [sourceBody] [targetBody])
    (appIH : ∀ (s t : State C F) (sv tv : Value) (sa ta : List Value),
      s.clock < source.clock → StateRel s t → ValueRel s.maxApp sv tv →
      List.Forall₂ (ValueRel s.maxApp) sa ta → sa.length ≤ s.maxApp →
      resultRel (List.Forall₂ (ValueRel s.maxApp)) (ValueRel s.maxApp)
        (evaluateApps sv sa s).1 (evaluateApp none tv ta t).1 ∧
      StateRel (evaluateApps sv sa s).2 (evaluateApp none tv ta t).2)
    (run : evaluate [.app trace location targetHead targetArgs] targetEnv target = (targetResult, targetFinal))
    (envRel : List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv)
    (states : StateRel source target)
    (code : CodeRel source.maxApp sourceCode [.app trace location targetHead targetArgs]) :
    ∃ sourceResult sourceFinal,
      evaluate sourceCode sourceEnv source = (sourceResult, sourceFinal) ∧
      resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
        sourceResult targetResult ∧ StateRel sourceFinal targetFinal := by
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .app trace location targetHead targetArgs := by
        simpa [introList] using code.2.symm
      obtain ⟨head, arg, collectedArgs, collectedHead, expressionEq, locationEq,
        collected, targetHeadEq, targetArgsEq⟩ :=
        introExp_eq_app source.maxApp expression trace location targetHead targetArgs unary transformed
      subst expression
      subst location
      have sourceArgsIH : EvaluateRelAt (C := C) (F := F) collectedArgs
          (introList source.maxApp collectedArgs) := by
        rw [← targetArgsEq]
        exact argsIH collectedArgs
      have sourceHeadIH : EvaluateRelAt (C := C) (F := F) [collectedHead]
          [introExp source.maxApp collectedHead] := by
        rw [← targetHeadEq]
        exact headIH collectedHead
      have related := evaluate_introApp_step source target sourceEnv targetEnv trace head arg collectedArgs
        collectedHead states envRel unary collected sourceArgsIH sourceHeadIH bodyIH appIH
      rw [transformed, run] at related
      cases sourceRun : evaluate [.app trace none head [arg]] sourceEnv source with
      | mk sourceResult sourceFinal =>
        rw [sourceRun] at related
        exact ⟨sourceResult, sourceFinal, rfl, related.1, related.2⟩

end Flapjack.Compiler.Backend.ClosMti

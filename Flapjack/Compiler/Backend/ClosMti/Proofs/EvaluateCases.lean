import Flapjack.Compiler.Backend.ClosMti.Proofs.Applications
import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallConst
import Flapjack.SemanticPrimitivesProps.ResultRelation

/-! Expression cases of the multi-argument introduction evaluation simulation. -/
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

/-- Introduction preserves the outer tick constructor on unary source code. -/
theorem introExp_eq_tick (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (targetBody : ClosLang.Exp) (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .tick trace targetBody) :
    ∃ body, expression = .tick trace body ∧ ClosProps.noMti body ∧
      targetBody = introExp maxApp body := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Introduction preserves the outer raise constructor on unary source code. -/
theorem introExp_eq_raise (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (targetBody : ClosLang.Exp) (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .raise trace targetBody) :
    ∃ body, expression = .raise trace body ∧ ClosProps.noMti body ∧
      targetBody = introExp maxApp body := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Introduction preserves the outer let constructor and transforms its
bindings and body independently. -/
theorem introExp_eq_let (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (targetBindings : List ClosLang.Exp) (targetBody : ClosLang.Exp)
    (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .let trace targetBindings targetBody) :
    ∃ bindings body, expression = .let trace bindings body ∧
      ClosProps.noMtiList bindings ∧ ClosProps.noMti body ∧
      targetBindings = introList maxApp bindings ∧ targetBody = introExp maxApp body := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Introduction preserves an exception handler and transforms both bodies. -/
theorem introExp_eq_handle (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (targetBody targetHandler : ClosLang.Exp) (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .handle trace targetBody targetHandler) :
    ∃ body handler, expression = .handle trace body handler ∧
      ClosProps.noMti body ∧ ClosProps.noMti handler ∧
      targetBody = introExp maxApp body ∧ targetHandler = introExp maxApp handler := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Introduction preserves a conditional and transforms its three branches. -/
theorem introExp_eq_if (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (targetCondition targetYes targetNo : ClosLang.Exp) (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .ifThenElse trace targetCondition targetYes targetNo) :
    ∃ condition yes no, expression = .ifThenElse trace condition yes no ∧
      ClosProps.noMti condition ∧ ClosProps.noMti yes ∧ ClosProps.noMti no ∧
      targetCondition = introExp maxApp condition ∧ targetYes = introExp maxApp yes ∧
      targetNo = introExp maxApp no := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Related closure values either decode to the same Boolean or both fail to
decode. -/
theorem valueRel_asBool {maxApp : Nat} {left right : Value}
    (related : ValueRel maxApp left right) : asBool left = asBool right := by
  cases related <;> try rfl
  case block tag left right fields =>
    cases fields with
    | nil => rfl
    | cons head tail =>
      cases tag with
      | zero => rfl
      | succ tag => cases tag <;> rfl

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

/-- Concatenating two pairs of related lists preserves their relation. -/
theorem forall₂_append_lists {A B : Type} {rel : A → B → Prop}
    {left leftTail : List A} {right rightTail : List B}
    (first : List.Forall₂ rel left right) (second : List.Forall₂ rel leftTail rightTail) :
    List.Forall₂ rel (left ++ leftTail) (right ++ rightTail) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact .cons head ih

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

/-- The tick case either times out in both states or invokes the body
induction hypothesis after decrementing both clocks. -/
theorem evaluateRel_tick {C F : Type} (trace : BackendCommon.Tra) (targetBody : ClosLang.Exp)
    (bodyIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode [targetBody])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelAt C F sourceCode [.tick trace targetBody] := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .tick trace targetBody := by
        simpa [introList] using code.2.symm
      obtain ⟨body, rfl, bodyUnary, bodyEq⟩ :=
        introExp_eq_tick source.maxApp expression trace targetBody unary transformed
      have clocks := (stateRel_clock_maxApp states).1
      by_cases zero : target.clock = 0
      · have sourceZero : source.clock = 0 := clocks.trans zero
        simp [evaluate, zero] at run
        obtain ⟨rfl, rfl⟩ := run
        exact ⟨.err (.abort .timeoutError), source, by simp [evaluate, sourceZero],
          by simp [resultRel, excRel], states⟩
      · have sourceNonzero : source.clock ≠ 0 := by simpa [clocks] using zero
        have decStates : StateRel (decClock 1 source) (decClock 1 target) := by
          obtain ⟨safe, sourceCode, targetCode, maxEq, positive, clockEq, ffi,
            globals, refs, compiler, oracle⟩ := states
          exact ⟨safe, sourceCode, targetCode, maxEq, positive,
            congrArg (fun clock => clock - 1) clockEq, ffi, globals, refs, compiler, oracle⟩
        have bodyCode : CodeRel (decClock 1 source).maxApp [body] [targetBody] := by
          simp [CodeRel, introList, bodyUnary, bodyEq, decClock]
        have targetRun : evaluate [targetBody] targetEnv (decClock 1 target) =
            (targetResult, targetFinal) := by simpa [evaluate, zero] using run
        obtain ⟨result, final, bodyRun, resultRel, finalStates⟩ :=
          bodyIH [body] targetEnv (decClock 1 target) sourceEnv targetFinal (decClock 1 source)
            targetResult targetRun env decStates bodyCode
        exact ⟨result, final, by simpa [evaluate, sourceNonzero] using bodyRun,
          resultRel, finalStates⟩

/-- Raising propagates related body errors or raises related singleton values. -/
theorem evaluateRel_raise {C F : Type} (trace : BackendCommon.Tra) (targetBody : ClosLang.Exp)
    (bodyIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode [targetBody])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelAt C F sourceCode [.raise trace targetBody] := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .raise trace targetBody := by
        simpa [introList] using code.2.symm
      obtain ⟨body, rfl, bodyUnary, bodyEq⟩ :=
        introExp_eq_raise source.maxApp expression trace targetBody unary transformed
      have bodyCode : CodeRel source.maxApp [body] [targetBody] := by
        simp [CodeRel, introList, bodyUnary, bodyEq]
      cases targetBodyRun : evaluate [targetBody] targetEnv target with
      | mk bodyResult targetMiddle =>
        obtain ⟨sourceBodyResult, sourceFinal, sourceBodyRun, bodyRel, finalStates⟩ :=
          bodyIH [body] targetEnv target sourceEnv targetMiddle source bodyResult
            targetBodyRun env states bodyCode
        cases bodyResult with
        | err targetError =>
          cases sourceBodyResult with
          | val values => simp [resultRel] at bodyRel
          | err sourceError =>
            rw [evaluate, targetBodyRun] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.err sourceError, sourceFinal, by rw [evaluate, sourceBodyRun],
              bodyRel, finalStates⟩
        | val targetValues =>
          cases sourceBodyResult with
          | err sourceError => simp [resultRel] at bodyRel
          | val sourceValues =>
            have targetLength := evaluate_length.1 [targetBody] targetEnv target targetMiddle
              targetValues targetBodyRun
            have sourceLength := evaluate_length.1 [body] sourceEnv source sourceFinal
              sourceValues sourceBodyRun
            cases targetValues with
            | nil => simp at targetLength
            | cons targetValue targetRest =>
              cases targetRest with
              | cons value tail => simp at targetLength
              | nil =>
                cases sourceValues with
                | nil => simp at sourceLength
                | cons sourceValue sourceRest =>
                  cases sourceRest with
                  | cons value tail => simp at sourceLength
                  | nil =>
                    have valueRel : ValueRel source.maxApp sourceValue targetValue := by
                      simpa [resultRel] using bodyRel
                    rw [evaluate, targetBodyRun] at run
                    simp only [Prod.mk.injEq] at run
                    obtain ⟨rfl, rfl⟩ := run
                    exact ⟨.err (.raise sourceValue), sourceFinal,
                      by rw [evaluate, sourceBodyRun]; rfl,
                      by simpa [resultRel, excRel] using valueRel, finalStates⟩

/-- Local bindings preserve the relation on the extended environments and
then use the body induction hypothesis. -/
theorem evaluateRel_let {C F : Type} (trace : BackendCommon.Tra)
    (targetBindings : List ClosLang.Exp) (targetBody : ClosLang.Exp)
    (bindingsIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode targetBindings)
    (bodyIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode [targetBody])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelAt C F sourceCode [.let trace targetBindings targetBody] := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .let trace targetBindings targetBody := by
        simpa [introList] using code.2.symm
      obtain ⟨bindings, body, rfl, bindingsUnary, bodyUnary, bindingsEq, bodyEq⟩ :=
        introExp_eq_let source.maxApp expression trace targetBindings targetBody unary transformed
      have bindingsCode : CodeRel source.maxApp bindings targetBindings :=
        ⟨ClosProps.noMtiList_iff bindings |>.mp bindingsUnary, bindingsEq⟩
      cases targetBindingsRun : evaluate targetBindings targetEnv target with
      | mk bindingsResult targetMiddle =>
        obtain ⟨sourceBindingsResult, sourceMiddle, sourceBindingsRun, bindingsRel, middleStates⟩ :=
          bindingsIH bindings targetEnv target sourceEnv targetMiddle source bindingsResult
            targetBindingsRun env states bindingsCode
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 bindings sourceEnv source
          simpa [sourceBindingsRun] using preserved
        cases bindingsResult with
        | err targetError =>
          cases sourceBindingsResult with
          | val values => simp [resultRel] at bindingsRel
          | err sourceError =>
            rw [evaluate, fixClock_evaluate, targetBindingsRun] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.err sourceError, sourceMiddle,
              by rw [evaluate, fixClock_evaluate, sourceBindingsRun], bindingsRel, middleStates⟩
        | val targetValues =>
          cases sourceBindingsResult with
          | err sourceError => simp [resultRel] at bindingsRel
          | val sourceValues =>
            have extended : List.Forall₂ (ValueRel sourceMiddle.maxApp)
                (sourceValues ++ sourceEnv) (targetValues ++ targetEnv) := by
              have values : List.Forall₂ (ValueRel sourceMiddle.maxApp) sourceValues targetValues := by
                simpa [resultRel, maxEq] using bindingsRel
              exact forall₂_append_lists values (by simpa [maxEq] using env)
            have bodyCode : CodeRel sourceMiddle.maxApp [body] [targetBody] := by
              simp [CodeRel, introList, bodyUnary, bodyEq, maxEq]
            have targetBodyRun : evaluate [targetBody] (targetValues ++ targetEnv) targetMiddle =
                (targetResult, targetFinal) := by
              rw [evaluate, fixClock_evaluate, targetBindingsRun] at run
              exact run
            obtain ⟨sourceResult, sourceFinal, sourceBodyRun, bodyRel, finalStates⟩ :=
              bodyIH [body] (targetValues ++ targetEnv) targetMiddle (sourceValues ++ sourceEnv)
                targetFinal sourceMiddle targetResult targetBodyRun extended middleStates bodyCode
            refine ⟨sourceResult, sourceFinal, ?_, ?_, finalStates⟩
            · rw [evaluate, fixClock_evaluate, sourceBindingsRun]
              exact sourceBodyRun
            · simpa [maxEq] using bodyRel

/-- Exception handlers preserve successful values and aborts, and run related
handlers when the bodies raise related values. -/
theorem evaluateRel_handle {C F : Type} (trace : BackendCommon.Tra)
    (targetBody targetHandler : ClosLang.Exp)
    (bodyIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode [targetBody])
    (handlerIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode [targetHandler])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelAt C F sourceCode [.handle trace targetBody targetHandler] := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .handle trace targetBody targetHandler := by
        simpa [introList] using code.2.symm
      obtain ⟨body, handler, rfl, bodyUnary, handlerUnary, bodyEq, handlerEq⟩ :=
        introExp_eq_handle source.maxApp expression trace targetBody targetHandler unary transformed
      have bodyCode : CodeRel source.maxApp [body] [targetBody] := by
        simp [CodeRel, introList, bodyUnary, bodyEq]
      cases targetBodyRun : evaluate [targetBody] targetEnv target with
      | mk bodyResult targetMiddle =>
        obtain ⟨sourceBodyResult, sourceMiddle, sourceBodyRun, bodyRel, middleStates⟩ :=
          bodyIH [body] targetEnv target sourceEnv targetMiddle source bodyResult
            targetBodyRun env states bodyCode
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 [body] sourceEnv source
          simpa [sourceBodyRun] using preserved
        cases bodyResult with
        | val targetValues =>
          cases sourceBodyResult with
          | err error => simp [resultRel] at bodyRel
          | val sourceValues =>
            rw [evaluate, fixClock_evaluate, targetBodyRun] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.val sourceValues, sourceMiddle,
              by rw [evaluate, fixClock_evaluate, sourceBodyRun], bodyRel, middleStates⟩
        | err targetError =>
          cases sourceBodyResult with
          | val values => simp [resultRel] at bodyRel
          | err sourceError =>
            cases targetError with
            | abort targetReason =>
              cases sourceError with
              | raise value => simp [resultRel, excRel] at bodyRel
              | abort sourceReason =>
                rw [evaluate, fixClock_evaluate, targetBodyRun] at run
                simp only [Prod.mk.injEq] at run
                obtain ⟨rfl, rfl⟩ := run
                exact ⟨.err (.abort sourceReason), sourceMiddle,
                  by rw [evaluate, fixClock_evaluate, sourceBodyRun], bodyRel, middleStates⟩
            | raise targetValue =>
              cases sourceError with
              | abort reason => simp [resultRel, excRel] at bodyRel
              | raise sourceValue =>
                have valueRel : ValueRel sourceMiddle.maxApp sourceValue targetValue := by
                  simpa [resultRel, excRel, maxEq] using bodyRel
                have extended : List.Forall₂ (ValueRel sourceMiddle.maxApp)
                    (sourceValue :: sourceEnv) (targetValue :: targetEnv) :=
                  .cons valueRel (by simpa [maxEq] using env)
                have handlerCode : CodeRel sourceMiddle.maxApp [handler] [targetHandler] := by
                  simp [CodeRel, introList, handlerUnary, handlerEq, maxEq]
                have targetHandlerRun : evaluate [targetHandler] (targetValue :: targetEnv) targetMiddle =
                    (targetResult, targetFinal) := by
                  rw [evaluate, fixClock_evaluate, targetBodyRun] at run
                  exact run
                obtain ⟨sourceResult, sourceFinal, sourceHandlerRun, handlerRel, finalStates⟩ :=
                  handlerIH [handler] (targetValue :: targetEnv) targetMiddle (sourceValue :: sourceEnv)
                    targetFinal sourceMiddle targetResult targetHandlerRun extended middleStates handlerCode
                refine ⟨sourceResult, sourceFinal, ?_, ?_, finalStates⟩
                · rw [evaluate, fixClock_evaluate, sourceBodyRun]
                  exact sourceHandlerRun
                · simpa [maxEq] using handlerRel

/-- Conditional evaluation takes corresponding branches on related Boolean
values, and rejects a non-Boolean condition on both sides. -/
theorem evaluateRel_if {C F : Type} (trace : BackendCommon.Tra)
    (targetCondition targetYes targetNo : ClosLang.Exp)
    (conditionIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode [targetCondition])
    (yesIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode [targetYes])
    (noIH : ∀ sourceCode, @EvaluateRelAt C F sourceCode [targetNo])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelAt C F sourceCode [.ifThenElse trace targetCondition targetYes targetNo] := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression =
          .ifThenElse trace targetCondition targetYes targetNo := by
        simpa [introList] using code.2.symm
      obtain ⟨condition, yes, no, rfl, conditionUnary, yesUnary, noUnary,
        conditionEq, yesEq, noEq⟩ :=
          introExp_eq_if source.maxApp expression trace targetCondition targetYes targetNo unary transformed
      have conditionCode : CodeRel source.maxApp [condition] [targetCondition] := by
        simp [CodeRel, introList, conditionUnary, conditionEq]
      cases targetConditionRun : evaluate [targetCondition] targetEnv target with
      | mk conditionResult targetMiddle =>
        obtain ⟨sourceConditionResult, sourceMiddle, sourceConditionRun, conditionRel, middleStates⟩ :=
          conditionIH [condition] targetEnv target sourceEnv targetMiddle source conditionResult
            targetConditionRun env states conditionCode
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 [condition] sourceEnv source
          simpa [sourceConditionRun] using preserved
        cases conditionResult with
        | err targetError =>
          cases sourceConditionResult with
          | val values => simp [resultRel] at conditionRel
          | err sourceError =>
            rw [evaluate, fixClock_evaluate, targetConditionRun] at run
            simp only [Prod.mk.injEq] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.err sourceError, sourceMiddle,
              by rw [evaluate, fixClock_evaluate, sourceConditionRun], conditionRel, middleStates⟩
        | val targetValues =>
          cases sourceConditionResult with
          | err sourceError => simp [resultRel] at conditionRel
          | val sourceValues =>
            have targetLength := evaluate_length.1 [targetCondition] targetEnv target targetMiddle
              targetValues targetConditionRun
            have sourceLength := evaluate_length.1 [condition] sourceEnv source sourceMiddle
              sourceValues sourceConditionRun
            cases targetValues with
            | nil => simp at targetLength
            | cons targetValue targetRest =>
              cases targetRest with
              | cons value tail => simp at targetLength
              | nil =>
                cases sourceValues with
                | nil => simp at sourceLength
                | cons sourceValue sourceRest =>
                  cases sourceRest with
                  | cons value tail => simp at sourceLength
                  | nil =>
                    have valueRel : ValueRel source.maxApp sourceValue targetValue := by
                      simpa [resultRel] using conditionRel
                    have sameBool := valueRel_asBool valueRel
                    have envMiddle : List.Forall₂ (ValueRel sourceMiddle.maxApp) sourceEnv targetEnv := by
                      simpa [maxEq] using env
                    cases boolRun : asBool targetValue with
                    | none =>
                      have sourceBool : asBool sourceValue = none := sameBool.trans boolRun
                      rw [evaluate, fixClock_evaluate, targetConditionRun] at run
                      simp [boolRun] at run
                      obtain ⟨rfl, rfl⟩ := run
                      refine ⟨.err (.abort .typeError), sourceMiddle, ?_, by simp [resultRel, excRel], middleStates⟩
                      rw [evaluate, fixClock_evaluate, sourceConditionRun]
                      simp [sourceBool]
                    | some conditionValue =>
                      have sourceBool : asBool sourceValue = some conditionValue := sameBool.trans boolRun
                      cases conditionValue with
                      | false =>
                        have branchCode : CodeRel sourceMiddle.maxApp [no] [targetNo] := by
                          simp [CodeRel, introList, noUnary, noEq, maxEq]
                        have targetBranchRun : evaluate [targetNo] targetEnv targetMiddle =
                            (targetResult, targetFinal) := by
                          rw [evaluate, fixClock_evaluate, targetConditionRun] at run
                          simpa [boolRun] using run
                        obtain ⟨sourceResult, sourceFinal, sourceRun, branchRel, finalStates⟩ :=
                          noIH [no] targetEnv targetMiddle sourceEnv targetFinal sourceMiddle targetResult
                            targetBranchRun envMiddle middleStates branchCode
                        refine ⟨sourceResult, sourceFinal, ?_, ?_, finalStates⟩
                        · rw [evaluate, fixClock_evaluate, sourceConditionRun]
                          simpa [sourceBool] using sourceRun
                        · simpa [maxEq] using branchRel
                      | true =>
                        have branchCode : CodeRel sourceMiddle.maxApp [yes] [targetYes] := by
                          simp [CodeRel, introList, yesUnary, yesEq, maxEq]
                        have targetBranchRun : evaluate [targetYes] targetEnv targetMiddle =
                            (targetResult, targetFinal) := by
                          rw [evaluate, fixClock_evaluate, targetConditionRun] at run
                          simpa [boolRun] using run
                        obtain ⟨sourceResult, sourceFinal, sourceRun, branchRel, finalStates⟩ :=
                          yesIH [yes] targetEnv targetMiddle sourceEnv targetFinal sourceMiddle targetResult
                            targetBranchRun envMiddle middleStates branchCode
                        refine ⟨sourceResult, sourceFinal, ?_, ?_, finalStates⟩
                        · rw [evaluate, fixClock_evaluate, sourceConditionRun]
                          simpa [sourceBool] using sourceRun
                        · simpa [maxEq] using branchRel

end Flapjack.Compiler.Backend.ClosMti

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

/-- The target-driven simulation restricted to a maximum source clock.
This interface lets structural induction hypotheses be used inside a
clock-first mutual induction; it is Lean-side proof infrastructure. -/
def EvaluateRelWithin {C F : Type} (limit : Nat) (sourceCode targetCode : List ClosLang.Exp) : Prop :=
  ∀ (targetEnv : List Value) (target : State C F) (sourceEnv : List Value)
    (targetFinal : State C F) (source : State C F)
    (targetResult : SemanticPrimitivesHOL.Result (List Value) Value),
    source.clock ≤ limit → evaluate targetCode targetEnv target = (targetResult, targetFinal) →
    List.Forall₂ (ValueRel source.maxApp) sourceEnv targetEnv →
    StateRel source target → CodeRel source.maxApp sourceCode targetCode →
    ∃ sourceResult sourceFinal,
      evaluate sourceCode sourceEnv source = (sourceResult, sourceFinal) ∧
      resultRel (List.Forall₂ (ValueRel source.maxApp)) (ValueRel source.maxApp)
        sourceResult targetResult ∧ StateRel sourceFinal targetFinal

/-- An unrestricted simulation is valid at any clock bound. -/
theorem evaluateRelAt_within {C F : Type} (limit : Nat) (sourceCode targetCode : List ClosLang.Exp)
    (simulation : EvaluateRelAt (C := C) (F := F) sourceCode targetCode) :
    EvaluateRelWithin (C := C) (F := F) limit sourceCode targetCode := by
  intro targetEnv target sourceEnv targetFinal source targetResult _
  exact simulation targetEnv target sourceEnv targetFinal source targetResult

/-- A simulation valid at one bound is valid at every smaller bound. -/
theorem evaluateRelWithin_mono {C F : Type} {lower upper : Nat}
    {sourceCode targetCode : List ClosLang.Exp} (bound : lower ≤ upper)
    (simulation : EvaluateRelWithin (C := C) (F := F) upper sourceCode targetCode) :
    EvaluateRelWithin (C := C) (F := F) lower sourceCode targetCode := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock
  exact simulation targetEnv target sourceEnv targetFinal source targetResult (by omega)

/-- A unary source expression can transform into a variable only if it was
the same variable. -/
theorem introExp_eq_var (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (index : Nat) (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .var trace index) : expression = .var trace index := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]

/-- Unary source code cannot transform into a direct call. -/
theorem introExp_ne_call (maxApp : Nat) (expression : ClosLang.Exp) (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (unary : ClosProps.noMti expression) :
    introExp maxApp expression ≠ .call trace ticks location args := by
  intro transformed
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

/-- A transformed function comes from an unannotated unary source function;
argument collection determines the target arity and body. -/
theorem introExp_eq_fn (maxApp : Nat) (expression : ClosLang.Exp)
    (name : Basis.Pure.MlString.MlString) (location : Option Nat) (vars : Option (List Nat))
    (arity : Nat) (targetBody : ClosLang.Exp) (unary : ClosProps.noMti expression)
    (transformed : introExp maxApp expression = .fn name location vars arity targetBody) :
    ∃ body rest, expression = .fn name none none 1 body ∧ ClosProps.noMti body ∧
      location = none ∧ vars = none ∧ collectArgs maxApp 1 body = (arity, rest) ∧
      targetBody = introExp maxApp rest := by
  cases expression <;>
    simp_all [ClosProps.noMti, introExp_var, introExp_if, introExp_let, introExp_raise,
      introExp_handle, introExp_tick, introExp_op, introExp_app_none,
      introExp_fn_none, introExp_letrec_none]
  case fn sourceName sourceLocation sourceVars sourceArity sourceBody =>
    cases found : collectArgs maxApp 1 sourceBody with
    | mk count body =>
      simp_all

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

/-- The direct-call case is unreachable under the unary source invariant. -/
theorem evaluateRel_call {C F : Type} (sourceCode : List ClosLang.Exp)
    (trace : BackendCommon.Tra) (ticks location : Nat) (args : List ClosLang.Exp) :
    @EvaluateRelAt C F sourceCode [.call trace ticks location args] := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .call trace ticks location args := by
        simpa [introList] using code.2.symm
      exact (introExp_ne_call source.maxApp expression trace ticks location args unary transformed).elim

/-- The multi-expression case composes simulations at a common clock bound. -/
theorem evaluateRel_consWithin {C F : Type} (limit : Nat) (targetHead targetSecond : ClosLang.Exp)
    (targetTail : List ClosLang.Exp)
    (headIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetHead])
    (tailIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode (targetSecond :: targetTail))
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelWithin C F limit sourceCode (targetHead :: targetSecond :: targetTail) := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock run env states code
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
            clock targetHeadRun env states parts.1
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 [sourceHead] sourceEnv source
          simpa [sourceHeadRun] using preserved
        have envMiddle : List.Forall₂ (ValueRel sourceMiddle.maxApp) sourceEnv targetEnv := by
          simpa [maxEq] using env
        have tailCode : CodeRel sourceMiddle.maxApp (sourceSecond :: sourceTail)
            (targetSecond :: targetTail) := by simpa [maxEq] using parts.2
        have middleClock : sourceMiddle.clock ≤ limit := by
          have preserved := evaluate_clock_le [sourceHead] sourceEnv source
          simp only [sourceHeadRun] at preserved
          omega
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
                          sourceMiddle targetTailResult middleClock targetTailRun envMiddle middleStates tailCode
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

/-- The tick case preserves a clock-bounded simulation. -/
theorem evaluateRel_tickWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra)
    (targetBody : ClosLang.Exp)
    (bodyIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetBody])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelWithin C F limit sourceCode [.tick trace targetBody] := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock run env states code
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
            targetResult (by simp [decClock]; omega) targetRun env decStates bodyCode
        exact ⟨result, final, by simpa [evaluate, sourceNonzero] using bodyRun,
          resultRel, finalStates⟩

/-- Raising preserves a clock-bounded simulation of its body. -/
theorem evaluateRel_raiseWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra)
    (targetBody : ClosLang.Exp)
    (bodyIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetBody])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelWithin C F limit sourceCode [.raise trace targetBody] := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock run env states code
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
            clock targetBodyRun env states bodyCode
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

/-- Local bindings preserve a clock-bounded simulation. -/
theorem evaluateRel_letWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra)
    (targetBindings : List ClosLang.Exp) (targetBody : ClosLang.Exp)
    (bindingsIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode targetBindings)
    (bodyIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetBody])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelWithin C F limit sourceCode [.let trace targetBindings targetBody] := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock run env states code
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
            clock targetBindingsRun env states bindingsCode
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 bindings sourceEnv source
          simpa [sourceBindingsRun] using preserved
        have middleClock : sourceMiddle.clock ≤ limit := by
          have preserved := evaluate_clock_le bindings sourceEnv source
          simp only [sourceBindingsRun] at preserved
          omega
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
                targetFinal sourceMiddle targetResult middleClock targetBodyRun extended middleStates bodyCode
            refine ⟨sourceResult, sourceFinal, ?_, ?_, finalStates⟩
            · rw [evaluate, fixClock_evaluate, sourceBindingsRun]
              exact sourceBodyRun
            · simpa [maxEq] using bodyRel

/-- Exception handlers preserve a clock-bounded simulation. -/
theorem evaluateRel_handleWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra)
    (targetBody targetHandler : ClosLang.Exp)
    (bodyIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetBody])
    (handlerIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetHandler])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelWithin C F limit sourceCode [.handle trace targetBody targetHandler] := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock run env states code
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
            clock targetBodyRun env states bodyCode
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 [body] sourceEnv source
          simpa [sourceBodyRun] using preserved
        have middleClock : sourceMiddle.clock ≤ limit := by
          have preserved := evaluate_clock_le [body] sourceEnv source
          simp only [sourceBodyRun] at preserved
          omega
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
                    targetFinal sourceMiddle targetResult middleClock targetHandlerRun extended middleStates handlerCode
                refine ⟨sourceResult, sourceFinal, ?_, ?_, finalStates⟩
                · rw [evaluate, fixClock_evaluate, sourceBodyRun]
                  exact sourceHandlerRun
                · simpa [maxEq] using handlerRel

/-- Conditional evaluation preserves a clock-bounded simulation. -/
theorem evaluateRel_ifWithin {C F : Type} (limit : Nat) (trace : BackendCommon.Tra)
    (targetCondition targetYes targetNo : ClosLang.Exp)
    (conditionIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetCondition])
    (yesIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetYes])
    (noIH : ∀ sourceCode, @EvaluateRelWithin C F limit sourceCode [targetNo])
    (sourceCode : List ClosLang.Exp) :
    @EvaluateRelWithin C F limit sourceCode [.ifThenElse trace targetCondition targetYes targetNo] := by
  intro targetEnv target sourceEnv targetFinal source targetResult clock run env states code
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
            clock targetConditionRun env states conditionCode
        have maxEq : sourceMiddle.maxApp = source.maxApp := by
          have preserved := ClosProps.evaluate_const.1 [condition] sourceEnv source
          simpa [sourceConditionRun] using preserved
        have middleClock : sourceMiddle.clock ≤ limit := by
          have preserved := evaluate_clock_le [condition] sourceEnv source
          simp only [sourceConditionRun] at preserved
          omega
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
                            middleClock targetBranchRun envMiddle middleStates branchCode
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
                            middleClock targetBranchRun envMiddle middleStates branchCode
                        refine ⟨sourceResult, sourceFinal, ?_, ?_, finalStates⟩
                        · rw [evaluate, fixClock_evaluate, sourceConditionRun]
                          simpa [sourceBool] using sourceRun
                        · simpa [maxEq] using branchRel

/-- Collected unary functions evaluate to related source and target closures. -/
theorem evaluateRel_fn {C F : Type} (name : Basis.Pure.MlString.MlString)
    (location : Option Nat) (vars : Option (List Nat)) (arity : Nat)
    (targetBody : ClosLang.Exp) (sourceCode : List ClosLang.Exp) :
    @EvaluateRelAt C F sourceCode [.fn name location vars arity targetBody] := by
  intro targetEnv target sourceEnv targetFinal source targetResult run env states code
  have length := codeRel_length code
  cases sourceCode with
  | nil => simp at length
  | cons expression rest =>
    cases rest with
    | cons next tail => simp at length
    | nil =>
      have unary : ClosProps.noMti expression := code.1 expression (by simp)
      have transformed : introExp source.maxApp expression = .fn name location vars arity targetBody := by
        simpa [introList] using code.2.symm
      obtain ⟨body, remaining, rfl, bodyUnary, rfl, rfl, collected, targetBodyEq⟩ :=
        introExp_eq_fn source.maxApp expression name location vars arity targetBody unary transformed
      have maxPos : 1 ≤ source.maxApp := by
        have agreement := stateRel_clock_maxApp states
        omega
      have arityBounds := collectArgsBounds source.maxApp 1 body arity remaining collected maxPos
      obtain ⟨names, bodyEq, arityEq, remainingUnary⟩ :=
        collectArgsUnary source.maxApp 1 body arity remaining collected bodyUnary
      have targetMax : target.maxApp = source.maxApp := (stateRel_clock_maxApp states).2.1.symm
      have targetBound : arity ≤ target.maxApp := by simpa [targetMax] using arityBounds.2
      have arityNonzero : arity ≠ 0 := by omega
      have closureCode : CodeRel source.maxApp [remaining] [targetBody] := by
        simp [CodeRel, introList, remainingUnary, targetBodyEq]
      have closures : ValueRel source.maxApp
          (.closure none [] sourceEnv 1 body) (.closure none [] targetEnv arity targetBody) := by
        rw [bodyEq]
        have result := ValueRel.closure [] [] sourceEnv targetEnv arity remaining targetBody names
          (by simpa using arityEq.symm) closureCode env List.Forall₂.nil
        simpa using result
      simp [evaluate, targetBound, arityNonzero] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨.val [.closure none [] sourceEnv 1 body], source, ?_, ?_, states⟩
      · simp [evaluate, maxPos]
      · simpa [resultRel] using List.Forall₂.cons closures List.Forall₂.nil

end Flapjack.Compiler.Backend.ClosMti

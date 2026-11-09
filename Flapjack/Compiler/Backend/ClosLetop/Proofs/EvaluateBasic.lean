module

public import Flapjack.Compiler.Backend.ClosLetop.Proofs.EvaluateLet
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBoolean

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import all Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateFuel
@[expose] public section

/-! Basic cases of closure let-operation correctness. -/
namespace Flapjack.Compiler.Backend.ClosLetop
open ClosSem
open Flapjack.SemanticPrimitivesHOL (Result)

namespace BasicPort
/-- The closure state's canonical finite-map representation roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end BasicPort

/-- Empty expression lists evaluate to related empty results. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_nil {C F : Type} (env nextEnv : List Value)
    (source : State C F) (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (target : State C F)
    (premises : evaluate [] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧ CodeRel [] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, _, states, code⟩ := premises
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  simp [CodeRel, compileList] at code
  subst targetCode
  exact ⟨.val [], target, by simp [evaluate], .nil, states⟩

/-- Related environments have related optional results at every index. This
lookup lemma is Lean-side infrastructure, not a standalone HOL declaration. -/
theorem environment_lookup (env nextEnv : List Value) (related : List.Forall₂ ValueRel env nextEnv)
    (index : Nat) : Flapjack.optionRel ValueRel env[index]? nextEnv[index]? := by
  induction related generalizing index with
  | nil => simp [Flapjack.optionRel]
  | cons head tail ih =>
    cases index with
    | zero => simpa [Flapjack.optionRel] using head
    | succ index => simpa using ih index

/-- Variables read related values, or both evaluations report a type error. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_var {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env nextEnv : List Value) (source : State C F) (result : Result (List Value) Value)
    (sourceNext : State C F) (targetCode : List ClosLang.Exp) (target : State C F)
    (premises : evaluate [.var trace index] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.var trace index] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.var trace index] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  have lookup := environment_lookup env nextEnv envRel index
  cases found : env[index]? with
  | none =>
    cases nextFound : nextEnv[index]? with
    | some value => simp [Flapjack.optionRel, found, nextFound] at lookup
    | none =>
      simp [evaluate, found] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.err (.abort .typeError), target, by simp [evaluate, nextFound], rfl, states⟩
  | some value =>
    cases nextFound : nextEnv[index]? with
    | none => simp [Flapjack.optionRel, found, nextFound] at lookup
    | some nextValue =>
      have values : ValueRel value nextValue := by
        simpa [Flapjack.optionRel, found, nextFound] using lookup
      simp [evaluate, found] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.val [nextValue], target, by simp [evaluate, nextFound], .cons values .nil, states⟩

/-- A nonempty sequence simulates its first expression and then its tail. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_cons {C F : Type} (first second : ClosLang.Exp)
    (rest : List ClosLang.Exp) (env : List Value) (source : State C F)
    (firstIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [first] env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel [first] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (restIH : ∀ (values : List Value) (middle : State C F),
      evaluate [first] env source = (.val values, middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate (second :: rest) env middle = (result, next) ∧
          List.Forall₂ ValueRel env nextEnv ∧ StateRel middle target ∧ CodeRel (second :: rest) code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate (first :: second :: rest) env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel (first :: second :: rest) targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = compileSing first :: compileList (second :: rest) := by
    simpa [CodeRel, compileList] using code
  rw [codeEq]
  cases firstRun : evaluate [first] env source with
  | mk firstResult middle =>
    cases firstResult with
    | err error =>
      rw [ClosProps.evaluate_cons_error first (second :: rest) env source middle error firstRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
        firstIH (.err error) sourceNext [compileSing first] nextEnv target
          ⟨firstRun, envRel, states, by simp [CodeRel, compileList]⟩
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at related
      | err targetError =>
        exact ⟨.err targetError, targetMiddle,
          ClosProps.evaluate_cons_error _ _ _ _ _ _ targetRun, related, middleRel⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value first env source middle values firstRun
      obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
        firstIH (.val [value]) middle [compileSing first] nextEnv target
          ⟨firstRun, envRel, states, by simp [CodeRel, compileList]⟩
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val targetValues =>
        cases related with
        | cons valueRel tailRel =>
          cases tailRel
          rename_i targetValue
          rw [ClosProps.evaluate_cons_value first (second :: rest) env source middle value firstRun] at run
          cases restRun : evaluate (second :: rest) env middle with
          | mk restResult last =>
            rw [restRun] at run
            obtain ⟨targetRestResult, targetLast, targetRestRun, restRel, lastRel⟩ :=
              restIH [value] middle firstRun restResult last (compileList (second :: rest))
                nextEnv targetMiddle ⟨restRun, envRel, middleRel, rfl⟩
            cases restResult with
            | err error =>
              simp only at run
              cases run
              cases targetRestResult with
              | val values => cases error <;> simp [ResultRel] at restRel
              | err targetError =>
                refine ⟨.err targetError, targetLast, ?_, restRel, lastRel⟩
                rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ targetRun, targetRestRun]
            | val values =>
              simp only at run
              cases run
              cases targetRestResult with
              | err error => cases error <;> simp [ResultRel] at restRel
              | val targetValues =>
                refine ⟨.val (targetValue :: targetValues), targetLast, ?_, ?_, lastRel⟩
                · rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ targetRun, targetRestRun]
                · exact .cons valueRel restRel

/-- Raising preserves related exceptions and propagates errors from its body. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_raise {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List Value) (source : State C F)
    (bodyIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [body] env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel [body] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.raise trace body] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.raise trace body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.raise trace (compileSing body)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult bodyNext =>
    obtain ⟨targetResult, targetNext, targetRun, related, nextRel⟩ :=
      bodyIH bodyResult bodyNext [compileSing body] nextEnv target
        ⟨bodyRun, envRel, states, by simp [CodeRel, compileList]⟩
    cases bodyResult with
    | err error =>
      simp [evaluate, bodyRun] at run
      obtain ⟨rfl, rfl⟩ := run
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at related
      | err targetError =>
        exact ⟨.err targetError, targetNext, by simp [evaluate, targetRun], related, nextRel⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value body env source bodyNext values bodyRun
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val targetValues =>
        cases related with
        | cons valueRel tailRel =>
          cases tailRel
          simp [evaluate, bodyRun] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨.err (.raise _), targetNext, by simp [evaluate, targetRun], valueRel, nextRel⟩

/-- Decrementing both clocks preserves the state relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "state_rel_dec_clock"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_dec_clock {C F : Type} (source target : State C F)
    (related : StateRel source target) : StateRel (decClock 1 source) (decClock 1 target) := by
  have clockEq : target.clock = source.clock := related.2.2.2.2.2.1
  simpa [StateRel, decClock, clockEq] using related

/-- A tick either times out on both sides or evaluates related bodies. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_tick {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List Value) (source : State C F)
    (bodyIH : source.clock ≠ 0 → ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [body] env (decClock 1 source) = (result, next) ∧
        List.Forall₂ ValueRel env nextEnv ∧ StateRel (decClock 1 source) target ∧
        CodeRel [body] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.tick trace body] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.tick trace body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.tick trace (compileSing body)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  have clockEq : target.clock = source.clock := states.2.2.2.2.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := clockEq.trans zero
    simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨.err (.abort .timeoutError), target, by simp [evaluate, targetZero], rfl, states⟩
  · have targetNonzero : target.clock ≠ 0 := by simpa [clockEq] using zero
    have bodyRun : evaluate [body] env (decClock 1 source) = (result, sourceNext) := by
      simpa [evaluate, zero] using run
    obtain ⟨targetResult, targetNext, targetRun, related, nextRel⟩ :=
      bodyIH zero result sourceNext [compileSing body] nextEnv (decClock 1 target)
        ⟨bodyRun, envRel, state_rel_dec_clock source target states, by simp [CodeRel, compileList]⟩
    exact ⟨targetResult, targetNext, by simpa [evaluate, targetNonzero] using targetRun, related, nextRel⟩

/-- Exception handling simulates the body and, when it raises, the handler
under environments extended by related exception values. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_handle {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List Value) (source : State C F)
    (bodyIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [body] env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel [body] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (handlerIH : ∀ (value : Value) (middle : State C F),
      evaluate [body] env source = (.err (.raise value), middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [handler] (value :: env) middle = (result, next) ∧
          List.Forall₂ ValueRel (value :: env) nextEnv ∧ StateRel middle target ∧
          CodeRel [handler] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.handle trace body handler] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.handle trace body handler] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.handle trace (compileSing body)
      (compileSing handler)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
      bodyIH bodyResult middle [compileSing body] nextEnv target
        ⟨bodyRun, envRel, states, by simp [CodeRel, compileList]⟩
    cases bodyResult with
    | val values =>
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val targetValues =>
        rw [evaluate, fixClock_evaluate, bodyRun] at run
        cases run
        exact ⟨.val targetValues, targetMiddle,
          by rw [evaluate, fixClock_evaluate, targetRun], related, middleRel⟩
    | err error =>
      cases error with
      | abort reason =>
        cases targetResult with
        | val values => simp [ResultRel] at related
        | err targetError =>
          cases targetError with
          | raise value => simp [ResultRel] at related
          | abort targetReason =>
            rw [evaluate, fixClock_evaluate, bodyRun] at run
            cases run
            exact ⟨.err (.abort targetReason), targetMiddle,
              by rw [evaluate, fixClock_evaluate, targetRun], related, middleRel⟩
      | raise value =>
        cases targetResult with
        | val values => simp [ResultRel] at related
        | err targetError =>
          cases targetError with
          | abort reason => simp [ResultRel] at related
          | raise targetValue =>
            have handlerRun : evaluate [handler] (value :: env) middle = (result, sourceNext) := by
              rw [evaluate, fixClock_evaluate, bodyRun] at run
              exact run
            obtain ⟨targetHandlerResult, targetLast, targetHandlerRun, handlerRel, lastRel⟩ :=
              handlerIH value middle bodyRun result sourceNext [compileSing handler]
                (targetValue :: nextEnv) targetMiddle
                ⟨handlerRun, .cons related envRel, middleRel, by simp [CodeRel, compileList]⟩
            refine ⟨targetHandlerResult, targetLast, ?_, handlerRel, lastRel⟩
            rw [evaluate, fixClock_evaluate, targetRun]
            exact targetHandlerRun

/-- The value relation preserves the Boolean observation used by conditionals.
This Lean-side helper has no standalone HOL declaration. -/
theorem valueRel_asBool {left right : Value} (related : ValueRel left right) :
    asBool left = asBool right := by
  cases related with
  | block tag left right entries =>
    cases entries with
    | nil => rfl
    | cons head tail => cases tag <;> simp [asBool]
  | number _ | word64 _ | byteVector _ | refPtr _ _ => rfl
  | closure => rfl
  | recclosure => rfl

/-- Conditional evaluation preserves both Boolean branches and the
type-error result for a non-Boolean condition. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_if {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List Value) (source : State C F)
    (conditionIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [condition] env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel [condition] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (yesIH : ∀ (values : List Value) (middle : State C F),
      evaluate [condition] env source = (.val values, middle) →
      boolValue true = @Flapjack.holHd Value ⟨unitValue⟩ values →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [yes] env middle = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
          StateRel middle target ∧ CodeRel [yes] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (noIH : ∀ (values : List Value) (middle : State C F),
      evaluate [condition] env source = (.val values, middle) →
      boolValue true ≠ @Flapjack.holHd Value ⟨unitValue⟩ values →
      boolValue false = @Flapjack.holHd Value ⟨unitValue⟩ values →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [no] env middle = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
          StateRel middle target ∧ CodeRel [no] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.ifThenElse trace condition yes no] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.ifThenElse trace condition yes no] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.ifThenElse trace (compileSing condition)
      (compileSing yes) (compileSing no)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  cases conditionRun : evaluate [condition] env source with
  | mk conditionResult middle =>
    obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
      conditionIH conditionResult middle [compileSing condition] nextEnv target
        ⟨conditionRun, envRel, states, by simp [CodeRel, compileList]⟩
    cases conditionResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, conditionRun] at run
      cases run
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at related
      | err targetError =>
        exact ⟨.err targetError, targetMiddle,
          by rw [evaluate, fixClock_evaluate, targetRun], related, middleRel⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value condition env source middle values conditionRun
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val targetValues =>
        cases related with
        | cons valueRel tailRel =>
          cases tailRel
          rename_i targetValue
          have boolEq : asBool value = asBool targetValue := valueRel_asBool valueRel
          cases decision : asBool value with
          | none =>
            have targetDecision : asBool targetValue = none := boolEq.symm.trans decision
            rw [evaluate, fixClock_evaluate, conditionRun] at run
            simp [decision] at run
            obtain ⟨rfl, rfl⟩ := run
            exact ⟨.err (.abort .typeError), targetMiddle,
              by rw [evaluate, fixClock_evaluate, targetRun]; simp [targetDecision], rfl, middleRel⟩
          | some flag =>
            have targetDecision : asBool targetValue = some flag := boolEq.symm.trans decision
            cases flag with
            | false =>
              have valueEq : boolValue false = value := ((asBool_eq_some value false).mp decision).symm
              have notTrue : boolValue true ≠ value := by
                rw [← valueEq]
                simp [boolValue, BackendCommon.trueTag, BackendCommon.falseTag]
              have branchRun : evaluate [no] env middle = (result, sourceNext) := by
                rw [evaluate, fixClock_evaluate, conditionRun] at run
                simpa [decision] using run
              obtain ⟨targetBranchResult, targetLast, targetBranchRun, branchRel, lastRel⟩ :=
                noIH [value] middle conditionRun (by simpa [Flapjack.holHd] using notTrue)
                  (by simpa [Flapjack.holHd] using valueEq) result sourceNext
                  [compileSing no] nextEnv targetMiddle
                  ⟨branchRun, envRel, middleRel, by simp [CodeRel, compileList]⟩
              refine ⟨targetBranchResult, targetLast, ?_, branchRel, lastRel⟩
              rw [evaluate, fixClock_evaluate, targetRun]
              simpa [targetDecision] using targetBranchRun
            | true =>
              have valueEq : boolValue true = value := ((asBool_eq_some value true).mp decision).symm
              have branchRun : evaluate [yes] env middle = (result, sourceNext) := by
                rw [evaluate, fixClock_evaluate, conditionRun] at run
                simpa [decision] using run
              obtain ⟨targetBranchResult, targetLast, targetBranchRun, branchRel, lastRel⟩ :=
                yesIH [value] middle conditionRun (by simpa [Flapjack.holHd] using valueEq)
                  result sourceNext [compileSing yes] nextEnv targetMiddle
                  ⟨branchRun, envRel, middleRel, by simp [CodeRel, compileList]⟩
              refine ⟨targetBranchResult, targetLast, ?_, branchRel, lastRel⟩
              rw [evaluate, fixClock_evaluate, targetRun]
              simpa [targetDecision] using targetBranchRun

/-- Capturing the same indices in related environments either fails on both
sides or returns related values, in order. This Lean-side helper has no standalone HOL declaration. -/
theorem environment_lookupVars (indices : List Nat) (env nextEnv : List Value)
    (related : List.Forall₂ ValueRel env nextEnv) :
    Flapjack.optionRel (List.Forall₂ ValueRel) (lookupVars indices env) (lookupVars indices nextEnv) := by
  induction indices with
  | nil => simp [lookupVars, Flapjack.optionRel]
  | cons index rest ih =>
    have head := environment_lookup env nextEnv related index
    cases left : env[index]? <;> cases right : nextEnv[index]? <;>
      simp [Flapjack.optionRel, left, right] at head
    · simp [lookupVars, left, right, Flapjack.optionRel]
    · rename_i value nextValue
      cases leftTail : lookupVars rest env <;> cases rightTail : lookupVars rest nextEnv <;>
        simp [Flapjack.optionRel, leftTail, rightTail] at ih
      · simp [lookupVars, left, right, leftTail, rightTail, Flapjack.optionRel]
      · simp [lookupVars, left, right, leftTail, rightTail, Flapjack.optionRel, head, ih]

/-- Function construction preserves closure values and both capture and
arity errors. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_fn {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env nextEnv : List Value) (source : State C F) (result : Result (List Value) Value)
    (sourceNext : State C F) (targetCode : List ClosLang.Exp) (target : State C F)
    (premises : evaluate [.fn name location selected arity body] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.fn name location selected arity body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.fn name location selected arity
      (compileSing body)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  have maxEq : target.maxApp = source.maxApp := states.2.2.2.1
  cases selected with
  | none =>
    by_cases arityOk : arity ≤ source.maxApp ∧ arity ≠ 0
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨.val [.closure location [] nextEnv arity (compileSing body)],
        target, ?_, ?_, states⟩
      · simp [evaluate, maxEq, arityOk]
      · exact .cons (.closure location [] [] env nextEnv arity body _ envRel .nil (by
          simp [CodeRel, compileList])) .nil
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.err (.abort .typeError), target, by simp [evaluate, maxEq, arityOk], rfl, states⟩
  | some indices =>
    by_cases arityOk : arity ≤ source.maxApp ∧ arity ≠ 0
    · have captureRel := environment_lookupVars indices env nextEnv envRel
      cases capture : lookupVars indices env with
      | none =>
        cases nextCapture : lookupVars indices nextEnv with
        | none =>
          simp [evaluate, arityOk, capture] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨.err (.abort .typeError), target,
            by simp [evaluate, maxEq, arityOk, nextCapture], rfl, states⟩
        | some values => simp [capture, nextCapture, Flapjack.optionRel] at captureRel
      | some values =>
        cases nextCapture : lookupVars indices nextEnv with
        | none => simp [capture, nextCapture, Flapjack.optionRel] at captureRel
        | some nextValues =>
          have captures : List.Forall₂ ValueRel values nextValues := by
            simpa [capture, nextCapture, Flapjack.optionRel] using captureRel
          simp [evaluate, arityOk, capture] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨.val [.closure location [] nextValues arity
            (compileSing body)], target, ?_, ?_, states⟩
          · simp [evaluate, maxEq, arityOk, nextCapture]
          · exact .cons (.closure location [] [] values nextValues arity body _ captures .nil (by
              simp [CodeRel, compileList])) .nil
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.err (.abort .typeError), target, by simp [evaluate, maxEq, arityOk], rfl, states⟩

/-- Application first evaluates arguments, then the function, and finally
uses the application induction hypothesis on the related values. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_app {C F : Type} (trace : BackendCommon.Tra)
    (location : Option Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (env : List Value) (source : State C F)
    (argsIH : 0 < args.length → ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (functionIH : ∀ (values : List Value) (middle : State C F),
      0 < args.length → evaluate args env source = (.val values, middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [function] env middle = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
          StateRel middle target ∧ CodeRel [function] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (appIH : ∀ (values : List Value) (middle : State C F) (functions : List Value) (last : State C F),
      0 < args.length → evaluate args env source = (.val values, middle) →
      evaluate [function] env middle = (.val functions, last) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (targetFunction : Value) (targetArgs : List Value) (target : State C F),
        evaluateApp location (@Flapjack.holHd Value ⟨unitValue⟩ functions) values last = (result, next) ∧
          ValueRel (@Flapjack.holHd Value ⟨unitValue⟩ functions) targetFunction ∧
          List.Forall₂ ValueRel values targetArgs ∧ StateRel last target →
        ∃ targetResult targetNext, evaluateApp location targetFunction targetArgs target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.app trace location function args] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.app trace location function args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.app trace location (compileSing function) (compileList args)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  cases args with
  | nil =>
    simp [evaluate] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨.err (.abort .typeError), target, by simp [compileList, evaluate], rfl, states⟩
  | cons first rest =>
    have nonempty : 0 < (first :: rest).length := by simp
    cases argsRun : evaluate (first :: rest) env source with
    | mk argsResult middle =>
      obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
        argsIH nonempty argsResult middle (compileList (first :: rest)) nextEnv target
          ⟨argsRun, envRel, states, rfl⟩
      cases argsResult with
      | err error =>
        rw [evaluate, fixClock_evaluate, argsRun] at run
        cases run
        cases targetArgsResult with
        | val values => cases error <;> simp [ResultRel] at argsRel
        | err targetError =>
          refine ⟨.err targetError, targetMiddle, ?_, argsRel, middleRel⟩
          simp only [compileList] at targetArgsRun ⊢
          rw [evaluate, fixClock_evaluate, targetArgsRun]
          rfl
      | val values =>
        cases targetArgsResult with
        | err error => cases error <;> simp [ResultRel] at argsRel
        | val targetValues =>
          cases functionRun : evaluate [function] env middle with
          | mk functionResult last =>
            obtain ⟨targetFunctionResult, targetLast, targetFunctionRun, functionRel, lastRel⟩ :=
              functionIH values middle nonempty argsRun functionResult last [compileSing function]
                nextEnv targetMiddle ⟨functionRun, envRel, middleRel, by simp [CodeRel, compileList]⟩
            cases functionResult with
            | err error =>
              rw [evaluate, fixClock_evaluate, argsRun] at run
              simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
              rw [fixClock_evaluate, functionRun] at run
              cases run
              cases targetFunctionResult with
              | val functions => cases error <;> simp [ResultRel] at functionRel
              | err targetError =>
                refine ⟨.err targetError, targetLast, ?_, functionRel, lastRel⟩
                simp only [compileList] at targetArgsRun ⊢
                rw [evaluate, fixClock_evaluate, targetArgsRun]
                simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                rw [fixClock_evaluate, targetFunctionRun]
            | val functions =>
              obtain ⟨value, rfl⟩ := evaluate_singleton_value function env middle last functions functionRun
              cases targetFunctionResult with
              | err error => cases error <;> simp [ResultRel] at functionRel
              | val targetFunctions =>
                cases functionRel with
                | cons valueRel tailRel =>
                  cases tailRel
                  rename_i targetValue
                  have appRun : evaluateApp location value values last = (result, sourceNext) := by
                    rw [evaluate, fixClock_evaluate, argsRun] at run
                    simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
                    rw [fixClock_evaluate, functionRun] at run
                    exact run
                  obtain ⟨targetResult, targetNext, targetRun, related, nextRel⟩ :=
                    appIH values middle [value] last nonempty argsRun functionRun result sourceNext
                      targetValue targetValues targetLast ⟨by simpa [Flapjack.holHd] using appRun,
                        valueRel, argsRel, lastRel⟩
                  refine ⟨targetResult, targetNext, ?_, related, nextRel⟩
                  simp only [compileList] at targetArgsRun ⊢
                  rw [evaluate, fixClock_evaluate, targetArgsRun]
                  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                  rw [fixClock_evaluate, targetFunctionRun]
                  exact targetRun

/-- Direct calls propagate argument errors or fail equally because related
states have empty installed code. -/
@[hol "cakeml/compiler/backend/proofs/clos_letopProofScript.sml" "evaluate_let_op"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_let_op_call {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List Value) (source : State C F)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.call trace ticks location args] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel [.call trace ticks location args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.call trace ticks location (compileList args)] := by
    simpa [CodeRel, compileList, compileSing] using code
  rw [codeEq]
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
      argsIH argsResult middle (compileList args) nextEnv target
        ⟨argsRun, envRel, states, rfl⟩
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at related
      | err targetError =>
        exact ⟨.err targetError, targetMiddle,
          by rw [evaluate, fixClock_evaluate, targetRun], related, middleRel⟩
    | val values =>
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at related
      | val targetValues =>
        have sourceEmpty : middle.code = HolFiniteMapExact.empty := middleRel.2.1
        have targetEmpty : targetMiddle.code = HolFiniteMapExact.empty := middleRel.2.2.1
        rw [evaluate, fixClock_evaluate, argsRun] at run
        simp [findCode, sourceEmpty, HolFiniteMapExact.empty] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨.err (.abort .typeError), targetMiddle, ?_, rfl, middleRel⟩
        rw [evaluate, fixClock_evaluate, targetRun]
        simp [findCode, targetEmpty, HolFiniteMapExact.empty]

end Flapjack.Compiler.Backend.ClosLetop

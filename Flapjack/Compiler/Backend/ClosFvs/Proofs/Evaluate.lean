module

public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Relations
public import Flapjack.Compiler.Backend.Semantics.ClosProps.SimpleRelations
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Primitive
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Install
public import Flapjack.Compiler.Backend.ClosFvs.Proofs.Force
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyBoolean
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClockShift
public import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallStep

@[expose] public section

/-! Evaluator cases for free-variable removal correctness. -/
namespace Flapjack.Compiler.Backend.ClosFvs
open Flapjack.Compiler.Backend.ClosSem
open Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Original result relation specialized to related lists and exceptions. -/
def ResultRel : Result (List Value) Value → Result (List Value) Value → Prop
  | .val left, .val right => List.Forall₂ ValueRel left right
  | .err (.raise left), .err (.raise right) => ValueRel left right
  | .err (.abort left), .err (.abort right) => left = right
  | _, _ => False

namespace EvaluatePort
/-- The closure state has the reviewed canonical finite-map roundtrip. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : StateBroad C F, (State.ofBroad s).toBroad = s) ∧
      (∀ s : State C F, State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluatePort

/-- Empty expression lists preserve the original evaluation result and state. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_nil {C F : Type} (env nextEnv : List Value)
    (source : State C F) (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (target : State C F)
    (premises : evaluate [] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, _, states, code⟩ := premises
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  simp [CodeRel, removeList] at code
  subst targetCode
  exact ⟨.val [], target, by simp [evaluate], .nil, states⟩

/-- Indexing related lists gives related optional entries. -/
theorem list_lookup_related {A B : Type} {relation : A → B → Prop} {left : List A} {right : List B}
    (related : List.Forall₂ relation left right) (index : Nat) :
    optionRel relation left[index]? right[index]? := by
  induction related generalizing index with
  | nil => simp [optionRel]
  | cons head tail ih =>
    cases index with
    | zero => simpa [optionRel] using head
    | succ index => simpa using ih index

/-- Capturing the same indices in related environments either fails on both
sides or returns related values, in order. -/
theorem environment_lookupVars (indices : List Nat) (env nextEnv : List Value)
    (related : List.Forall₂ ValueRel env nextEnv) :
    optionRel (List.Forall₂ ValueRel) (lookupVars indices env) (lookupVars indices nextEnv) := by
  induction indices with
  | nil => simp [lookupVars, optionRel]
  | cons index rest ih =>
    have head := list_lookup_related related index
    cases left : env[index]? <;> cases right : nextEnv[index]? <;>
      simp [optionRel, left, right] at head
    · simp [lookupVars, left, right, optionRel]
    · rename_i value nextValue
      cases leftTail : lookupVars rest env <;> cases rightTail : lookupVars rest nextEnv <;>
        simp [optionRel, leftTail, rightTail] at ih
      · simp [lookupVars, left, right, leftTail, rightTail, optionRel]
      · simp [lookupVars, left, right, leftTail, rightTail, optionRel, head, ih]

/-- A successful capture contains one value per selected index. -/
theorem lookupVars_length (indices : List Nat) (env values : List Value)
    (found : lookupVars indices env = some values) : values.length = indices.length := by
  induction indices generalizing values with
  | nil => simp [lookupVars] at found; subst values; rfl
  | cons index rest ih =>
    cases head : env[index]? with
    | none => simp [lookupVars, head] at found
    | some value =>
      cases tail : lookupVars rest env with
      | none => simp [lookupVars, head, tail] at found
      | some remaining =>
        simp [lookupVars, head, tail] at found
        subst values
        simp [ih remaining tail]

/-- Capture the whole environment or the explicitly selected indices. -/
def captureEnv {α : Type} (selected : Option (List Nat)) (env : List α) : Option (List α) :=
  match selected with | none => some env | some indices => lookupVars indices env

/-- Removing free variables from recursive functions preserves their arities
and relates each source body to its transformed body. -/
theorem removeFuns_related (count captured : Nat) (functions : List (Nat × ClosLang.Exp)) :
    List.Forall₂ (FunctionRel (captured + count)) functions (removeFuns count captured functions) := by
  induction functions with
  | nil => exact .nil
  | cons function rest ih =>
    rcases function with ⟨arity, body⟩
    apply List.Forall₂.cons
    · simp [FunctionRel, CodeRel, removeList, Nat.add_comm, Nat.add_left_comm]
    · simpa [removeFuns] using ih

/-- Arity checks are unaffected by rewriting recursive function bodies. -/
theorem removeFuns_all (count captured maxApp : Nat) (functions : List (Nat × ClosLang.Exp)) :
    (removeFuns count captured functions).all (fun (arity, _) => arity ≤ maxApp && arity != 0) =
      functions.all (fun (arity, _) => arity ≤ maxApp && arity != 0) := by
  simp [removeFuns_eq_map, Function.comp_def]

/-- Recursive closures generated from related bundles and environments are
related at each common index. -/
theorem recursive_bundle_related (location : Option Nat) (env nextEnv : List Value)
    (functions nextFunctions : List (Nat × ClosLang.Exp))
    (environments : List.Forall₂ ValueRel env nextEnv)
    (bodies : List.Forall₂ (FunctionRel (env.length + functions.length)) functions nextFunctions) :
    List.Forall₂ ValueRel
      ((List.range functions.length).map (fun i => Value.recclosure location [] env functions i))
      ((List.range nextFunctions.length).map (fun i => Value.recclosure location [] nextEnv nextFunctions i)) := by
  rw [← bodies.length_eq]
  generalize List.range functions.length = indices
  induction indices with
  | nil => exact .nil
  | cons index rest ih =>
    exact .cons (.recclosure location [] [] env nextEnv functions nextFunctions index environments .nil bodies) ih

/-- A source variable, including an out-of-scope one, is simulated by the
corresponding variable or generated type-error expression. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_var {C F : Type} (trace : BackendCommon.Tra) (index : Nat)
    (env nextEnv : List Value) (source : State C F) (result : Result (List Value) Value)
    (sourceNext : State C F) (targetCode : List ClosLang.Exp) (target : State C F)
    (premises : evaluate [.var trace index] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.var trace index] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have lookup := list_lookup_related envRel index
  cases found : env[index]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp found
    simp [evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run
    have codeEq : targetCode = [.op trace (.memOp .el) []] := by
      simpa [CodeRel, removeList, removeSing, Nat.not_lt.mpr outside] using code
    refine ⟨.err (.abort .typeError), target, ?_, rfl, states⟩
    rw [codeEq]
    simp [evaluate, doApp, applyMemory, fixClock]
  | some value =>
    have inside : index < env.length := by
      by_contra h
      have missing : env[index]? = none := List.getElem?_eq_none (Nat.le_of_not_gt h)
      simp [missing] at found
    cases nextFound : nextEnv[index]? with
    | none => simp [found, nextFound, optionRel] at lookup
    | some nextValue =>
      have values : ValueRel value nextValue := by simpa [found, nextFound, optionRel] using lookup
      simp [evaluate, found] at run
      obtain ⟨rfl, rfl⟩ := run
      have codeEq : targetCode = [.var trace index] := by
        simpa [CodeRel, removeList, removeSing, inside] using code
      refine ⟨.val [nextValue], target, ?_, .cons values .nil, states⟩
      rw [codeEq]
      simp [evaluate, nextFound]

/-- The nonempty sequencing case of the source evaluator induction. The tail
induction hypothesis is needed only after successful evaluation of the head. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_cons {C F : Type} (first second : ClosLang.Exp)
    (rest : List ClosLang.Exp) (env : List Value) (source : State C F)
    (firstIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [first] env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length [first] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (restIH : ∀ (values : List Value) (middle : State C F),
      evaluate [first] env source = (.val values, middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate (second :: rest) env middle = (result, next) ∧
          List.Forall₂ ValueRel env nextEnv ∧ StateRel middle target ∧
          CodeRel env.length (second :: rest) code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate (first :: second :: rest) env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length (first :: second :: rest) targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = removeSing env.length first :: removeList env.length (second :: rest) := by
    simpa [CodeRel, removeList] using code
  rw [codeEq]
  cases firstRun : evaluate [first] env source with
  | mk firstResult middle =>
    cases firstResult with
    | err error =>
      rw [ClosProps.evaluate_cons_error first (second :: rest) env source middle error firstRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
        firstIH (.err error) sourceNext [removeSing env.length first] nextEnv target
          ⟨firstRun, envRel, states, by simp [CodeRel, removeList]⟩
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at related
      | err targetError =>
        exact ⟨.err targetError, targetMiddle,
          ClosProps.evaluate_cons_error _ _ _ _ _ _ targetRun, related, middleRel⟩
    | val values =>
      obtain ⟨value, rfl⟩ := evaluate_singleton_value first env source middle values firstRun
      obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
        firstIH (.val [value]) middle [removeSing env.length first] nextEnv target
          ⟨firstRun, envRel, states, by simp [CodeRel, removeList]⟩
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
              restIH [value] middle firstRun restResult last (removeList env.length (second :: rest))
                nextEnv targetMiddle ⟨restRun, envRel, middleRel, by simp [CodeRel]⟩
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
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_raise {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List Value) (source : State C F)
    (bodyIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [body] env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length [body] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.raise trace body] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.raise trace body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.raise trace (removeSing env.length body)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult bodyNext =>
    obtain ⟨targetResult, targetNext, targetRun, related, nextRel⟩ :=
      bodyIH bodyResult bodyNext [removeSing env.length body] nextEnv target
        ⟨bodyRun, envRel, states, by simp [CodeRel, removeList]⟩
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
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "state_rel_dec_clock"
  (fmap_as_finite_support := [refs, code])]
theorem state_rel_dec_clock {C F : Type} (source target : State C F)
    (related : StateRel source target) : StateRel (decClock 1 source) (decClock 1 target) := by
  have clockEq : target.clock = source.clock := related.2.2.2.2.2.1
  simpa [StateRel, decClock, clockEq] using related

/-- A tick either times out on both sides or evaluates related bodies. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_tick {C F : Type} (trace : BackendCommon.Tra)
    (body : ClosLang.Exp) (env : List Value) (source : State C F)
    (bodyIH : source.clock ≠ 0 → ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [body] env (decClock 1 source) = (result, next) ∧
        List.Forall₂ ValueRel env nextEnv ∧ StateRel (decClock 1 source) target ∧
        CodeRel env.length [body] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.tick trace body] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.tick trace body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.tick trace (removeSing env.length body)] := by
    simpa [CodeRel, removeList, removeSing] using code
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
      bodyIH zero result sourceNext [removeSing env.length body] nextEnv (decClock 1 target)
        ⟨bodyRun, envRel, state_rel_dec_clock source target states, by simp [CodeRel, removeList]⟩
    exact ⟨targetResult, targetNext, by simpa [evaluate, targetNonzero] using targetRun, related, nextRel⟩

/-- Exception handling simulates the body and, when it raises, the handler
under environments extended by related exception values. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_handle {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (env : List Value) (source : State C F)
    (bodyIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [body] env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length [body] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (handlerIH : ∀ (value : Value) (middle : State C F),
      evaluate [body] env source = (.err (.raise value), middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [handler] (value :: env) middle = (result, next) ∧
          List.Forall₂ ValueRel (value :: env) nextEnv ∧ StateRel middle target ∧
          CodeRel (value :: env).length [handler] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.handle trace body handler] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.handle trace body handler] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.handle trace (removeSing env.length body)
      (removeSing (env.length + 1) handler)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
      bodyIH bodyResult middle [removeSing env.length body] nextEnv target
        ⟨bodyRun, envRel, states, by simp [CodeRel, removeList]⟩
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
              handlerIH value middle bodyRun result sourceNext [removeSing (env.length + 1) handler]
                (targetValue :: nextEnv) targetMiddle
                ⟨handlerRun, .cons related envRel, middleRel, by simp [CodeRel, removeList]⟩
            refine ⟨targetHandlerResult, targetLast, ?_, handlerRel, lastRel⟩
            rw [evaluate, fixClock_evaluate, targetRun]
            exact targetHandlerRun

/-- Let evaluates related bindings before extending both environments for
the related bodies, or propagates a binding error. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_let {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (env : List Value) (source : State C F)
    (bindingsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate bindings env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length bindings code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (bodyIH : ∀ (values : List Value) (middle : State C F),
      evaluate bindings env source = (.val values, middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [body] (values ++ env) middle = (result, next) ∧
          List.Forall₂ ValueRel (values ++ env) nextEnv ∧ StateRel middle target ∧
          CodeRel (values ++ env).length [body] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.let trace bindings body] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.let trace bindings body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.let trace (removeList env.length bindings)
      (removeSing (env.length + (removeList env.length bindings).length) body)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  cases bindingsRun : evaluate bindings env source with
  | mk bindingsResult middle =>
    obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
      bindingsIH bindingsResult middle (removeList env.length bindings) nextEnv target
        ⟨bindingsRun, envRel, states, by simp [CodeRel]⟩
    cases bindingsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, bindingsRun] at run
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
        have length : values.length = bindings.length :=
          (evaluate_length (C := C) (F := F)).1 bindings env source middle values bindingsRun
        have bodyRun : evaluate [body] (values ++ env) middle = (result, sourceNext) := by
          rw [evaluate, fixClock_evaluate, bindingsRun] at run
          exact run
        obtain ⟨targetBodyResult, targetLast, targetBodyRun, bodyRel, lastRel⟩ :=
          bodyIH values middle bindingsRun result sourceNext
            [removeSing (env.length + (removeList env.length bindings).length) body]
            (targetValues ++ nextEnv) targetMiddle
            ⟨bodyRun, List.rel_append related envRel, middleRel, by
              simp [CodeRel, removeList, removeList_length, length, Nat.add_comm]⟩
        refine ⟨targetBodyResult, targetLast, ?_, bodyRel, lastRel⟩
        rw [evaluate, fixClock_evaluate, targetRun]
        exact targetBodyRun

/-- The value relation preserves the Boolean observation used by conditionals. -/
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
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_if {C F : Type} (trace : BackendCommon.Tra)
    (condition yes no : ClosLang.Exp) (env : List Value) (source : State C F)
    (conditionIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate [condition] env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length [condition] code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (yesIH : ∀ (values : List Value) (middle : State C F),
      evaluate [condition] env source = (.val values, middle) →
      boolValue true = @Flapjack.holHd Value ⟨unitValue⟩ values →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [yes] env middle = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
          StateRel middle target ∧ CodeRel env.length [yes] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (noIH : ∀ (values : List Value) (middle : State C F),
      evaluate [condition] env source = (.val values, middle) →
      boolValue true ≠ @Flapjack.holHd Value ⟨unitValue⟩ values →
      boolValue false = @Flapjack.holHd Value ⟨unitValue⟩ values →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [no] env middle = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
          StateRel middle target ∧ CodeRel env.length [no] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.ifThenElse trace condition yes no] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.ifThenElse trace condition yes no] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.ifThenElse trace (removeSing env.length condition)
      (removeSing env.length yes) (removeSing env.length no)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  cases conditionRun : evaluate [condition] env source with
  | mk conditionResult middle =>
    obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
      conditionIH conditionResult middle [removeSing env.length condition] nextEnv target
        ⟨conditionRun, envRel, states, by simp [CodeRel, removeList]⟩
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
                  [removeSing env.length no] nextEnv targetMiddle
                  ⟨branchRun, envRel, middleRel, by simp [CodeRel, removeList]⟩
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
                  result sourceNext [removeSing env.length yes] nextEnv targetMiddle
                  ⟨branchRun, envRel, middleRel, by simp [CodeRel, removeList]⟩
              refine ⟨targetBranchResult, targetLast, ?_, branchRel, lastRel⟩
              rw [evaluate, fixClock_evaluate, targetRun]
              simpa [targetDecision] using targetBranchRun

/-- Function construction preserves closure values and both capture and
arity errors. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_fn {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp)
    (env nextEnv : List Value) (source : State C F) (result : Result (List Value) Value)
    (sourceNext : State C F) (targetCode : List ClosLang.Exp) (target : State C F)
    (premises : evaluate [.fn name location selected arity body] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.fn name location selected arity body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.fn name location selected arity
      (removeSing (arity + (selected.map List.length).getD env.length) body)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  have maxEq : target.maxApp = source.maxApp := states.2.2.2.1
  cases selected with
  | none =>
    by_cases arityOk : arity ≤ source.maxApp ∧ arity ≠ 0
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨.val [.closure location [] nextEnv arity (removeSing (arity + env.length) body)],
        target, ?_, ?_, states⟩
      · simp [evaluate, maxEq, arityOk]
      · exact .cons (.closure location [] [] env nextEnv arity body _ envRel .nil (by
          simp [CodeRel, removeList, Nat.add_comm])) .nil
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
        | some values => simp [capture, nextCapture, optionRel] at captureRel
      | some values =>
        cases nextCapture : lookupVars indices nextEnv with
        | none => simp [capture, nextCapture, optionRel] at captureRel
        | some nextValues =>
          have captures : List.Forall₂ ValueRel values nextValues := by
            simpa [capture, nextCapture, optionRel] using captureRel
          have length := lookupVars_length indices env values capture
          simp [evaluate, arityOk, capture] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨.val [.closure location [] nextValues arity
            (removeSing (arity + indices.length) body)], target, ?_, ?_, states⟩
          · simp [evaluate, maxEq, arityOk, nextCapture]
          · exact .cons (.closure location [] [] values nextValues arity body _ captures .nil (by
              simp [CodeRel, removeList, length, Nat.add_comm])) .nil
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.err (.abort .typeError), target, by simp [evaluate, maxEq, arityOk], rfl, states⟩

/-- Recursive closure construction preserves related environments and then
simulates the body under those environments. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_letrec {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat))
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (env : List Value) (source : State C F)
    (bodyIH : ∀ (buildRc : List Value → List Value) (envdelta : Option (List Value)) (ed : List Value),
      functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true →
      buildRc = (fun captured => (List.range functions.length).map
        (fun i => Value.recclosure location [] captured functions i)) →
      envdelta = (captureEnv selected env).map buildRc → envdelta = some ed →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [body] (ed ++ env) source = (result, next) ∧
          List.Forall₂ ValueRel (ed ++ env) nextEnv ∧ StateRel source target ∧
          CodeRel (ed ++ env).length [body] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.letrec names location selected functions body] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.letrec names location selected functions body] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.letrec names location selected
      (removeFuns functions.length (selected.map List.length |>.getD env.length) functions)
      (removeSing (functions.length + env.length) body)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  have maxEq : target.maxApp = source.maxApp := states.2.2.2.1
  have success : ∀ (captured nextCaptured : List Value),
      functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true →
      captureEnv selected env = some captured → captureEnv selected nextEnv = some nextCaptured →
      captured.length = (selected.map List.length).getD env.length →
      List.Forall₂ ValueRel captured nextCaptured →
      ∃ targetResult targetNext,
        evaluate [.letrec names location selected
          (removeFuns functions.length (selected.map List.length |>.getD env.length) functions)
          (removeSing (functions.length + env.length) body)] nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
    intro captured nextCaptured arityOk capture nextCapture length captures
    let recs := (List.range functions.length).map (fun i => Value.recclosure location [] captured functions i)
    let nextFunctions := removeFuns functions.length captured.length functions
    let nextRecs := (List.range nextFunctions.length).map
      (fun i => Value.recclosure location [] nextCaptured nextFunctions i)
    have recRel : List.Forall₂ ValueRel recs nextRecs :=
      recursive_bundle_related location captured nextCaptured functions nextFunctions captures
        (removeFuns_related functions.length captured.length functions)
    have bodyRun : evaluate [body] (recs ++ env) source = (result, sourceNext) := by
      rw [evaluate.eq_def] at run
      simp only [arityOk, ↓reduceIte] at run
      cases selected with
      | none =>
        change some env = some captured at capture
        cases capture
        simpa [recs] using run
      | some indices =>
        change lookupVars indices env = some captured at capture
        simpa [capture, recs] using run
    obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
      bodyIH (fun captured => (List.range functions.length).map
          (fun i => Value.recclosure location [] captured functions i)) (some recs) recs
        arityOk rfl (by simp [capture, recs]) rfl result sourceNext [removeSing (functions.length + env.length) body]
        (nextRecs ++ nextEnv) target
        ⟨bodyRun, List.rel_append recRel envRel, states, by
          simp [CodeRel, removeList, recs]⟩
    refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
    rw [evaluate.eq_def]
    simp only [maxEq, removeFuns_all, arityOk, ↓reduceIte]
    cases selected with
    | none =>
      change some nextEnv = some nextCaptured at nextCapture
      cases nextCapture
      simpa [nextFunctions, nextRecs, length] using targetRun
    | some indices =>
      change lookupVars indices nextEnv = some nextCaptured at nextCapture
      simpa [nextCapture, nextFunctions, nextRecs, length] using targetRun
  cases selected with
  | none =>
    by_cases arityOk : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true
    · exact success env nextEnv arityOk rfl rfl rfl envRel
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.err (.abort .typeError), target,
        by simp [evaluate, maxEq, removeFuns_all, arityOk], rfl, states⟩
  | some indices =>
    by_cases arityOk : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0) = true
    · have captureRel := environment_lookupVars indices env nextEnv envRel
      cases capture : lookupVars indices env with
      | none =>
        cases nextCapture : lookupVars indices nextEnv with
        | none =>
          simp [evaluate, arityOk, capture] at run
          obtain ⟨rfl, rfl⟩ := run
          exact ⟨.err (.abort .typeError), target,
            by simp [evaluate, maxEq, removeFuns_all, arityOk, nextCapture], rfl, states⟩
        | some values => simp [capture, nextCapture, optionRel] at captureRel
      | some values =>
        cases nextCapture : lookupVars indices nextEnv with
        | none => simp [capture, nextCapture, optionRel] at captureRel
        | some nextValues =>
          exact success values nextValues arityOk capture nextCapture
            (lookupVars_length indices env values capture) (by simpa [capture, nextCapture, optionRel] using captureRel)
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨.err (.abort .typeError), target,
        by simp [evaluate, maxEq, removeFuns_all, arityOk], rfl, states⟩

/-- Application first evaluates arguments, then the function, and finally
uses the application induction hypothesis on the related values. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_app {C F : Type} (trace : BackendCommon.Tra)
    (location : Option Nat) (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (env : List Value) (source : State C F)
    (argsIH : 0 < args.length → ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (functionIH : ∀ (values : List Value) (middle : State C F),
      0 < args.length → evaluate args env source = (.val values, middle) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [function] env middle = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
          StateRel middle target ∧ CodeRel env.length [function] code →
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
      CodeRel env.length [.app trace location function args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.app trace location (removeSing env.length function) (removeList env.length args)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  cases args with
  | nil =>
    simp [evaluate] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨.err (.abort .typeError), target, by simp [removeList, evaluate], rfl, states⟩
  | cons first rest =>
    have nonempty : 0 < (first :: rest).length := by simp
    cases argsRun : evaluate (first :: rest) env source with
    | mk argsResult middle =>
      obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
        argsIH nonempty argsResult middle (removeList env.length (first :: rest)) nextEnv target
          ⟨argsRun, envRel, states, by simp [CodeRel]⟩
      cases argsResult with
      | err error =>
        rw [evaluate, fixClock_evaluate, argsRun] at run
        cases run
        cases targetArgsResult with
        | val values => cases error <;> simp [ResultRel] at argsRel
        | err targetError =>
          refine ⟨.err targetError, targetMiddle, ?_, argsRel, middleRel⟩
          simp only [removeList] at targetArgsRun ⊢
          rw [evaluate, fixClock_evaluate, targetArgsRun]
          rfl
      | val values =>
        cases targetArgsResult with
        | err error => cases error <;> simp [ResultRel] at argsRel
        | val targetValues =>
          cases functionRun : evaluate [function] env middle with
          | mk functionResult last =>
            obtain ⟨targetFunctionResult, targetLast, targetFunctionRun, functionRel, lastRel⟩ :=
              functionIH values middle nonempty argsRun functionResult last [removeSing env.length function]
                nextEnv targetMiddle ⟨functionRun, envRel, middleRel, by simp [CodeRel, removeList]⟩
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
                simp only [removeList] at targetArgsRun ⊢
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
                  simp only [removeList] at targetArgsRun ⊢
                  rw [evaluate, fixClock_evaluate, targetArgsRun]
                  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                  rw [fixClock_evaluate, targetFunctionRun]
                  exact targetRun

/-- Direct calls propagate argument errors or fail equally because related
states have empty installed code. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_call {C F : Type} (trace : BackendCommon.Tra)
    (ticks location : Nat) (args : List ClosLang.Exp) (env : List Value) (source : State C F)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.call trace ticks location args] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.call trace ticks location args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.call trace ticks location (removeList env.length args)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    obtain ⟨targetResult, targetMiddle, targetRun, related, middleRel⟩ :=
      argsIH argsResult middle (removeList env.length args) nextEnv target
        ⟨argsRun, envRel, states, by simp [CodeRel]⟩
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

/-- Ordinary operations simulate after related argument evaluation. This
Flapjack helper isolates the non-install, non-forcing dispatcher branch of
the HOL operation case. -/
theorem evaluate_ordinary_op {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp) (env : List Value) (source : State C F)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.op trace op args] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.op trace op args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.op trace op (removeList env.length args)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq, evaluate_ordinaryOp_eq trace op _ _ _ notInstall notForce]
  rw [evaluate_ordinaryOp_eq trace op _ _ _ notInstall notForce] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
      argsIH argsResult middle (removeList env.length args) nextEnv target
        ⟨argsRun, envRel, states, by simp [CodeRel]⟩
    rw [argsRun] at run
    rw [targetArgsRun]
    cases argsResult with
    | err error =>
      cases run
      cases targetArgsResult with
      | val values => cases error <;> simp [ResultRel] at argsRel
      | err targetError => exact ⟨.err targetError, targetMiddle, rfl, argsRel, middleRel⟩
    | val values =>
      cases targetArgsResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val targetValues =>
        have step := PrimitivePort.doAppLemma middle targetMiddle values.reverse targetValues.reverse op
          ⟨middleRel, List.rel_reverse argsRel⟩
        cases appRun : doApp op values.reverse middle with
        | err error =>
          simp only [appRun] at step run
          cases run
          obtain ⟨targetError, targetApp, errors⟩ := step
          refine ⟨.err targetError, targetMiddle, ?_, ?_, middleRel⟩
          · simp [targetApp]
          · cases error <;> cases targetError <;>
              simp_all [ResultRel, Flapjack.SemanticPrimitivesProps.excRel]
        | val pair =>
          rcases pair with ⟨value, last⟩
          simp only [appRun] at step run
          cases run
          obtain ⟨targetValue, targetLast, valuesRel, lastRel, targetApp⟩ := step
          exact ⟨.val [targetValue], targetLast, by simp [targetApp], .cons valuesRel .nil, lastRel⟩

/-- Installing related code simulates errors and evaluation of the newly
installed, nonempty program. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_install {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (source : State C F)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (programIH : ∀ (values : List Value) (middle : State C F) (program : List ClosLang.Exp)
        (installed : State C F),
      evaluate args env source = (.val values, middle) →
      doInstall values.reverse middle = (.val program, installed) →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate program [] installed = (result, next) ∧ List.Forall₂ ValueRel [] nextEnv ∧
          StateRel installed target ∧ CodeRel 0 program code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.op trace .install args] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.op trace .install args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.op trace .install (removeList env.length args)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
      argsIH argsResult middle (removeList env.length args) nextEnv target
        ⟨argsRun, envRel, states, by simp [CodeRel]⟩
    cases argsResult with
    | err error =>
      rw [evaluate_install_eq, argsRun] at run
      cases run
      cases targetArgsResult with
      | val values => cases error <;> simp [ResultRel] at argsRel
      | err targetError =>
        exact ⟨.err targetError, targetMiddle,
          by rw [evaluate_install_eq, targetArgsRun], argsRel, middleRel⟩
    | val values =>
      cases targetArgsResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val targetValues =>
        have installRel := InstallPort.doInstallLemma middle targetMiddle values.reverse targetValues.reverse
          ⟨middleRel, List.rel_reverse argsRel⟩
        cases installRun : doInstall values.reverse middle with
        | mk installResult installed =>
          rw [installRun] at installRel
          cases installResult with
          | err error =>
            obtain ⟨targetError, targetInstalled, targetInstall, errors, installedRel⟩ := installRel
            rw [evaluate_install_eq, argsRun] at run
            simp only [runInstalled, installRun] at run
            cases run
            refine ⟨.err targetError, targetInstalled, ?_, ?_, installedRel⟩
            · rw [evaluate_install_eq, targetArgsRun]
              simp [runInstalled, targetInstall]
            · cases error <;> cases targetError <;>
                simp_all [ResultRel, Flapjack.SemanticPrimitivesProps.excRel]
          | val program =>
            obtain ⟨targetProgram, targetInstalled, installedRel, nonempty, programRel, targetInstall⟩ := installRel
            cases programRun : evaluate program [] installed with
            | mk programResult final =>
              obtain ⟨targetProgramResult, targetFinal, targetProgramRun, related, finalRel⟩ :=
                programIH values middle program installed argsRun installRun programResult final targetProgram []
                  targetInstalled ⟨programRun, .nil, installedRel, programRel⟩
              cases programResult with
              | err error =>
                rw [evaluate_install_eq, argsRun] at run
                simp only [runInstalled, installRun, programRun] at run
                cases run
                cases targetProgramResult with
                | val vals => cases error <;> simp [ResultRel] at related
                | err targetError =>
                  refine ⟨.err targetError, targetFinal, ?_, related, finalRel⟩
                  rw [evaluate_install_eq, targetArgsRun]
                  simp [runInstalled, targetInstall, targetProgramRun]
              | val returned =>
                cases targetProgramResult with
                | err error => cases error <;> simp [ResultRel] at related
                | val targetReturned =>
                  have returnedNonempty : returned ≠ [] := by
                    intro empty
                    subst returned
                    have length := (evaluate_length (C := C) (F := F)).1 program [] installed final [] programRun
                    exact nonempty (List.eq_nil_of_length_eq_zero length.symm)
                  have lastRel := forall₂_holLast related returnedNonempty
                  rw [evaluate_install_eq, argsRun] at run
                  simp only [runInstalled, installRun, programRun] at run
                  cases run
                  refine ⟨.val [@Flapjack.holLast Value ⟨unitValue⟩ targetReturned], targetFinal,
                    ?_, .cons lastRel .nil, finalRel⟩
                  rw [evaluate_install_eq, targetArgsRun]
                  simp [runInstalled, targetInstall, targetProgramRun]

/-- Forcing simulates thunk inspection, the generated call, and its update. -/
@[hol "cakeml/compiler/backend/proofs/clos_fvsProofScript.sml" "evaluate_remove_fvs"
  (fmap_as_finite_support := [refs, code])]
theorem evaluate_remove_fvs_force {C F : Type} (trace : BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List Value) (source : State C F)
    (argsIH : ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
      evaluate args env source = (result, next) ∧ List.Forall₂ ValueRel env nextEnv ∧
        StateRel source target ∧ CodeRel env.length args code →
      ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
        ResultRel result targetResult ∧ StateRel next targetNext)
    (forceIH : ∀ (values : List Value) (middle : State C F) (value : Value),
      evaluate args env source = (.val values, middle) →
      destThunk values middle.refs = .isThunk .notEvaluated value →
      ∀ (result : Result (List Value) Value) (next : State C F)
        (code : List ClosLang.Exp) (nextEnv : List Value) (target : State C F),
        evaluate [appUnit (.var .none 0)] [value] middle = (result, next) ∧
          List.Forall₂ ValueRel [value] nextEnv ∧ StateRel middle target ∧
          CodeRel 1 [appUnit (.var .none 0)] code →
        ∃ targetResult targetNext, evaluate code nextEnv target = (targetResult, targetNext) ∧
          ResultRel result targetResult ∧ StateRel next targetNext)
    (result : Result (List Value) Value) (sourceNext : State C F)
    (targetCode : List ClosLang.Exp) (nextEnv : List Value) (target : State C F)
    (premises : evaluate [.op trace (.thunkOp .forceThunk) args] env source = (result, sourceNext) ∧
      List.Forall₂ ValueRel env nextEnv ∧ StateRel source target ∧
      CodeRel env.length [.op trace (.thunkOp .forceThunk) args] targetCode) :
    ∃ targetResult targetNext,
      evaluate targetCode nextEnv target = (targetResult, targetNext) ∧
      ResultRel result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨run, envRel, states, code⟩ := premises
  have codeEq : targetCode = [.op trace (.thunkOp .forceThunk) (removeList env.length args)] := by
    simpa [CodeRel, removeList, removeSing] using code
  rw [codeEq]
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
      argsIH argsResult middle (removeList env.length args) nextEnv target
        ⟨argsRun, envRel, states, by simp [CodeRel]⟩
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      cases targetArgsResult with
      | val values => cases error <;> simp [ResultRel] at argsRel
      | err targetError =>
        exact ⟨.err targetError, targetMiddle,
          by rw [evaluate, fixClock_evaluate, targetArgsRun], argsRel, middleRel⟩
    | val values =>
      cases targetArgsResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val targetValues =>
        have inspected := destThunk_list_related middle targetMiddle values targetValues argsRel middleRel
        rw [evaluate, fixClock_evaluate, argsRun] at run
        dsimp only at run
        cases sourceThunk : destThunk values middle.refs with
        | badRef =>
          cases targetThunk : destThunk targetValues targetMiddle.refs <;>
            simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          rw [sourceThunk] at run
          cases run
          refine ⟨.err (.abort .typeError), targetMiddle, ?_, rfl, middleRel⟩
          rw [evaluate, fixClock_evaluate, targetArgsRun]
          dsimp only
          rw [targetThunk]
          simp
        | notThunk =>
          cases targetThunk : destThunk targetValues targetMiddle.refs <;>
            simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          rw [sourceThunk] at run
          cases run
          refine ⟨.err (.abort .typeError), targetMiddle, ?_, rfl, middleRel⟩
          rw [evaluate, fixClock_evaluate, targetArgsRun]
          dsimp only
          rw [targetThunk]
          simp
        | isThunk mode value =>
          cases targetThunk : destThunk targetValues targetMiddle.refs with
          | badRef => simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          | notThunk => simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          | isThunk targetMode targetValue =>
            have rel : mode = targetMode ∧ ValueRel value targetValue := by
              simpa [DestThunkRel, sourceThunk, targetThunk] using inspected
            obtain ⟨rfl, valueRel⟩ := rel
            cases mode with
            | evaluated =>
              rw [sourceThunk] at run
              cases run
              refine ⟨.val [targetValue], targetMiddle, ?_, .cons valueRel .nil, middleRel⟩
              rw [evaluate, fixClock_evaluate, targetArgsRun]
              dsimp only
              rw [targetThunk]
            | notEvaluated =>
              cases forceRun : evaluate [appUnit (.var .none 0)] [value] middle with
              | mk forceResult last =>
                obtain ⟨targetForceResult, targetLast, targetForceRun, forceRel, lastRel⟩ :=
                  forceIH values middle value argsRun sourceThunk forceResult last [appUnit (.var .none 0)]
                    [targetValue] targetMiddle ⟨forceRun, .cons valueRel .nil, middleRel,
                      by simp [CodeRel, removeList, removeSing, appUnit]⟩
                cases forceResult with
                | err error =>
                  rw [sourceThunk] at run
                  dsimp only at run
                  rw [forceRun] at run
                  cases run
                  cases targetForceResult with
                  | val vals => cases error <;> simp [ResultRel] at forceRel
                  | err targetError =>
                    refine ⟨.err targetError, targetLast, ?_, forceRel, lastRel⟩
                    rw [evaluate, fixClock_evaluate, targetArgsRun]
                    dsimp only
                    rw [targetThunk]
                    dsimp only
                    rw [targetForceRun]
                | val forced =>
                  cases targetForceResult with
                  | err error => cases error <;> simp [ResultRel] at forceRel
                  | val targetForced =>
                    have update := updateThunk_related last targetLast values targetValues forced targetForced
                      argsRel forceRel lastRel
                    cases updateRun : updateThunk values last.refs forced with
                    | none =>
                      have targetUpdate : updateThunk targetValues targetLast.refs targetForced = none := by
                        simpa [updateRun] using update
                      rw [sourceThunk] at run
                      dsimp only at run
                      rw [forceRun] at run
                      dsimp only at run
                      rw [updateRun] at run
                      cases run
                      refine ⟨.err (.abort .typeError), targetLast, ?_, rfl, lastRel⟩
                      rw [evaluate, fixClock_evaluate, targetArgsRun]
                      dsimp only
                      rw [targetThunk]
                      dsimp only
                      rw [targetForceRun]
                      dsimp only
                      rw [targetUpdate]
                      simp
                    | some refs =>
                      rw [updateRun] at update
                      obtain ⟨targetRefs, targetUpdate, updatedRel⟩ := update
                      rw [sourceThunk] at run
                      dsimp only at run
                      rw [forceRun] at run
                      dsimp only at run
                      rw [updateRun] at run
                      cases run
                      refine ⟨.val targetForced, { targetLast with refs := targetRefs }, ?_, forceRel, updatedRel⟩
                      rw [evaluate, fixClock_evaluate, targetArgsRun]
                      dsimp only
                      rw [targetThunk]
                      dsimp only
                      rw [targetForceRun]
                      dsimp only
                      rw [targetUpdate]

end Flapjack.Compiler.Backend.ClosFvs

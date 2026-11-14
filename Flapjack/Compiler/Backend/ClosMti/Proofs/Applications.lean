module

public import Flapjack.Compiler.Backend.ClosMti.Proofs.CollectApps
public import Flapjack.Compiler.Backend.ClosMti.Proofs.StateRelation
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Mathlib.Data.List.Induction

@[expose] public section

/-! Application-reconstruction lemmas for the closure evaluator. -/
namespace Flapjack.Compiler.Backend.ClosMti
open Flapjack.SemanticPrimitivesHOL

/-- An error while evaluating the argument of a unary application propagates. -/
theorem unaryApp_arg_error {C F : Type} (trace : BackendCommon.Tra)
    (function arg : ClosLang.Exp) (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (error : ErrorResult ClosSem.Value)
    (run : ClosSem.evaluate [arg] env state = (.err error, next)) :
    ClosSem.evaluate [.app trace none function [arg]] env state = (.err error, next) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, run]
  rfl

/-- An error in a unary application's function propagates after its argument. -/
theorem unaryApp_function_error {C F : Type} (trace : BackendCommon.Tra)
    (function arg : ClosLang.Exp) (env : List ClosSem.Value) (state middle next : ClosSem.State C F)
    (value : ClosSem.Value) (error : ErrorResult ClosSem.Value)
    (argRun : ClosSem.evaluate [arg] env state = (.val [value], middle))
    (functionRun : ClosSem.evaluate [function] env middle = (.err error, next)) :
    ClosSem.evaluate [.app trace none function [arg]] env state = (.err error, next) := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argRun]
  dsimp only
  rw [ClosSem.fixClock_evaluate, functionRun]
  rfl

/-- A successful unary argument and function proceed to closure application. -/
theorem unaryApp_success {C F : Type} (trace : BackendCommon.Tra)
    (function arg : ClosLang.Exp) (env : List ClosSem.Value) (state middle next : ClosSem.State C F)
    (value fn : ClosSem.Value)
    (argRun : ClosSem.evaluate [arg] env state = (.val [value], middle))
    (functionRun : ClosSem.evaluate [function] env middle = (.val [fn], next)) :
    ClosSem.evaluate [.app trace none function [arg]] env state = ClosSem.evaluateApp none fn [value] next := by
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate, argRun]
  dsimp only
  rw [ClosSem.fixClock_evaluate, functionRun]
  rfl

namespace EvaluateAppsWitness
/-- The closure state uses the canonical finite-map representation. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ state : ClosSem.StateBroad C F, (ClosSem.State.ofBroad state).toBroad = state) ∧
      (∀ state : ClosSem.State C F, ClosSem.State.ofBroad state.toBroad = state) :=
  ClosSem.holFmapAsFiniteSupportWitness
end EvaluateAppsWitness

/-- Apply collected values in the same order as nested unary applications. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "evaluate_apps_def"
  (fmap_as_finite_support := [refs, code])]
noncomputable def evaluateApps {C F : Type} (fn : ClosSem.Value) :
    List ClosSem.Value → ClosSem.State C F → ClosSem.EvalResult C F
  | [], state => (.val [fn], state)
  | x :: xs, state =>
    match evaluateApps fn xs state with
    | (.val [value], next) => ClosSem.evaluateApp none value [x] next
    | result => result

/-- Successful reconstructed application chains return exactly one value. -/
theorem evaluateApps_singleton {C F : Type} (fn : ClosSem.Value) (args : List ClosSem.Value)
    (state next : ClosSem.State C F) (values : List ClosSem.Value)
    (run : evaluateApps fn args state = (.val values, next)) : ∃ value, values = [value] := by
  induction args generalizing state next values with
  | nil =>
    simp [evaluateApps] at run
    obtain ⟨rfl, _⟩ := run
    exact ⟨fn, rfl⟩
  | cons x xs ih =>
    cases previous : evaluateApps fn xs state with
    | mk result middle =>
      cases result with
      | err error => simp [evaluateApps, previous] at run
      | val inner =>
        obtain ⟨value, rfl⟩ := ih state middle inner previous
        have appRun : ClosSem.evaluateApp none value [x] middle = (.val values, next) := by
          simpa [evaluateApps, previous] using run
        have length := ClosSem.evaluate_length.2 none value [x] middle next values appRun
        cases values with
        | nil => simp at length
        | cons value tail =>
          cases tail with
          | nil => exact ⟨value, rfl⟩
          | cons other tail => simp at length

/-- Applying the last argument first decomposes a reconstructed application
chain. This uses the Lean evaluator; its HOL correspondence remains open. -/
theorem evaluateApps_snoc {C F : Type} (args : List ClosSem.Value) (x fn : ClosSem.Value)
    (state : ClosSem.State C F) :
    evaluateApps fn (args ++ [x]) state =
      match ClosSem.evaluateApp none fn [x] state with
      | (.val [value], next) => evaluateApps value args next
      | result => result := by
  induction args generalizing fn state with
  | nil =>
    simp only [List.nil_append, evaluateApps]
    cases h : ClosSem.evaluateApp none fn [x] state with
    | mk result next =>
      cases result with
      | err error => rfl
      | val values =>
        cases values with
        | nil => rfl
        | cons value rest =>
          cases rest <;> rfl
  | cons y ys ih =>
    simp only [List.cons_append, evaluateApps, ih]
    cases h : ClosSem.evaluateApp none fn [x] state with
    | mk result next =>
      cases result with
      | err error => rfl
      | val values =>
        cases values with
        | nil => rfl
        | cons value rest =>
          cases rest <;> rfl

/-- A failed closure lookup for the final argument stops the whole chain
with the original state and a type error. -/
theorem evaluateApps_snoc_badClosure {C F : Type} (args : List ClosSem.Value)
    (x fn : ClosSem.Value) (state : ClosSem.State C F)
    (bad : ClosSem.destClosure state.maxApp none fn [x] = none) :
    evaluateApps fn (args ++ [x]) state = (.err (.abort .typeError), state) := by
  have badApp : ClosSem.evaluateApp none fn [x] state = (.err (.abort .typeError), state) := by
    rw [ClosSem.evaluateApp]
    split <;> simp_all
  rw [evaluateApps_snoc]
  rw [badApp]

/-- Applying one argument to a unary closure whose body is another function
captures that argument and consumes one clock tick. This is a property of the
current Lean evaluator, whose HOL correspondence remains open. -/
theorem evaluateApp_nestedFn {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (body : ClosLang.Exp) (env : List ClosSem.Value) (x : ClosSem.Value)
    (state : ClosSem.State C F) (maxApp : 1 ≤ state.maxApp) (clock : 1 ≤ state.clock) :
    ClosSem.evaluateApp none (.closure none [] env 1 (.fn name none none 1 body)) [x] state =
      (.val [.closure none [] (x :: env) 1 body], ClosSem.decClock 1 state) := by
  rw [ClosSem.evaluateApp]
  split
  · simp_all [ClosSem.destClosure, ClosSem.checkLoc]
  · simp_all [ClosSem.destClosure, ClosSem.checkLoc]
  · rename_i expression captured rest found
    simp [ClosSem.destClosure, ClosSem.checkLoc, maxApp] at found
    obtain ⟨rfl, rfl, rfl⟩ := found
    have nonzero : state.clock ≠ 0 := by omega
    simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.decClock, maxApp, nonzero,
      ClosSem.evaluateApp]

/-- A unary closure with a clock tick available evaluates its body with the
argument added to its environment. The evaluator correspondence is pending. -/
theorem evaluateApp_unary {C F : Type} (body : ClosLang.Exp) (env : List ClosSem.Value)
    (x : ClosSem.Value) (state : ClosSem.State C F)
    (maxApp : 1 ≤ state.maxApp) (clock : 1 ≤ state.clock) :
    ClosSem.evaluateApp none (.closure none [] env 1 body) [x] state =
      ClosSem.evaluate [body] (x :: env) (ClosSem.decClock 1 state) := by
  rw [ClosSem.evaluateApp]
  split
  · simp_all [ClosSem.destClosure, ClosSem.checkLoc]
  · simp_all [ClosSem.destClosure, ClosSem.checkLoc]
  · rename_i expression captured rest found
    simp [ClosSem.destClosure, ClosSem.checkLoc, maxApp] at found
    obtain ⟨rfl, rfl, rfl⟩ := found
    have nonzero : state.clock ≠ 0 := by omega
    simp only [List.length_cons, List.length_nil, Nat.sub_zero, Nat.zero_add,
      Nat.lt_one_iff, nonzero, ↓reduceIte]
    rw [ClosSem.fixClock_evaluate]
    cases run : ClosSem.evaluate [body] (x :: env) (ClosSem.decClock 1 state) with
    | mk result next =>
      cases result with
      | err error => rfl
      | val values =>
        cases values with
        | nil => rfl
        | cons value rest =>
          cases rest with
          | nil => simp [ClosSem.evaluateApp]
          | cons other rest => rfl

/-- Applying no more arguments than there are nested unary functions captures
them in order and consumes one tick per argument. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "evaluate_apps_Clos_short"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApps_nestedFns_short {C F : Type} (args : List ClosSem.Value)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (state : ClosSem.State C F)
    (body : ClosLang.Exp) (env : List ClosSem.Value)
    (premises : args.length ≤ state.clock ∧ args.length ≤ names.length ∧ 1 ≤ state.maxApp) :
    evaluateApps (.closure none [] env 1 (mkFns names body)) args state =
      (.val [.closure none [] (args ++ env) 1 (mkFns (names.drop args.length) body)],
        ClosSem.decClock args.length state) := by
  obtain ⟨clock, lengths, maxApp⟩ := premises
  induction args using List.reverseRecOn generalizing names env state with
  | nil => simp [evaluateApps, ClosSem.decClock]
  | append_singleton args x ih =>
    cases names with
    | nil => simp at lengths
    | cons name names =>
      have clockOne : 1 ≤ state.clock := by simp at clock; omega
      have tailClock : args.length ≤ (ClosSem.decClock 1 state).clock := by
        simp [ClosSem.decClock] at *; omega
      have tailLength : args.length ≤ names.length := by simp at lengths; omega
      have tailMax : 1 ≤ (ClosSem.decClock 1 state).maxApp := by
        simpa [ClosSem.decClock] using maxApp
      rw [evaluateApps_snoc]
      simp only [mkFns]
      rw [evaluateApp_nestedFn name (mkFns names body) env x state maxApp clockOne]
      simp only
      rw [ih names (ClosSem.decClock 1 state) (x :: env) tailClock tailLength tailMax]
      simp [List.length_append, ClosSem.decClock, List.append_assoc, Nat.sub_sub,
        Nat.add_comm]

/-- A unary closure application with no remaining clock times out before
evaluating its body. -/
theorem evaluateApp_unary_timeout {C F : Type}
    (body : ClosLang.Exp) (env : List ClosSem.Value) (x : ClosSem.Value)
    (state : ClosSem.State C F) (maxApp : 1 ≤ state.maxApp) (clock : state.clock = 0) :
    ClosSem.evaluateApp none (.closure none [] env 1 body) [x] state =
      (.err (.abort .timeoutError), { state with clock := 0 }) := by
  rw [ClosSem.evaluateApp]
  split
  · simp_all [ClosSem.destClosure, ClosSem.checkLoc]
  · simp_all [ClosSem.destClosure, ClosSem.checkLoc]
  · rename_i expression captured rest found
    simp [ClosSem.destClosure, ClosSem.checkLoc, maxApp] at found
    obtain ⟨rfl, rfl, rfl⟩ := found
    simp [clock]

/-- If the clock runs out while consuming nested unary functions, the
reconstructed chain returns the timeout and leaves its clock at zero. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "evaluate_apps_Clos_timeout"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApps_nestedFns_timeout {C F : Type} (args : List ClosSem.Value)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (state : ClosSem.State C F)
    (body : ClosLang.Exp) (env : List ClosSem.Value)
    (premises : state.clock < args.length ∧ args.length ≤ names.length ∧ 1 ≤ state.maxApp) :
    evaluateApps (.closure none [] env 1 (mkFns names body)) args state =
      (.err (.abort .timeoutError), { state with clock := 0 }) := by
  obtain ⟨clock, lengths, maxApp⟩ := premises
  induction args using List.reverseRecOn generalizing names env state with
  | nil => simp at clock
  | append_singleton args x ih =>
    cases names with
    | nil => simp at lengths
    | cons name names =>
      rw [evaluateApps_snoc]
      simp only [mkFns]
      by_cases zero : state.clock = 0
      · rw [evaluateApp_unary_timeout (.fn name none none 1 (mkFns names body)) env x state maxApp zero]
      · have clockOne : 1 ≤ state.clock := by omega
        have tailClock : (ClosSem.decClock 1 state).clock < args.length := by
          simp [ClosSem.decClock] at *; omega
        have tailLength : args.length ≤ names.length := by simp at lengths; omega
        have tailMax : 1 ≤ (ClosSem.decClock 1 state).maxApp := by
          simpa [ClosSem.decClock] using maxApp
        rw [evaluateApp_nestedFn name (mkFns names body) env x state maxApp clockOne]
        simp only
        rw [ih names (ClosSem.decClock 1 state) (x :: env) tailClock tailLength tailMax]
        simp [ClosSem.decClock]

/-- Timeout also occurs before reaching the final body when there are more
arguments than nested functions and the clock is no larger than their count. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "evaluate_apps_Clos_timeout_alt"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApps_nestedFns_timeout_long {C F : Type} (args : List ClosSem.Value)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (state : ClosSem.State C F)
    (body : ClosLang.Exp) (env : List ClosSem.Value)
    (premises : state.clock ≤ names.length ∧ names.length < args.length ∧ 1 ≤ state.maxApp) :
    evaluateApps (.closure none [] env 1 (mkFns names body)) args state =
      (.err (.abort .timeoutError), { state with clock := 0 }) := by
  obtain ⟨clock, lengths, maxApp⟩ := premises
  induction args using List.reverseRecOn generalizing names env state with
  | nil => simp at lengths
  | append_singleton args x ih =>
    rw [evaluateApps_snoc]
    cases names with
    | nil =>
      have zero : state.clock = 0 := by simp at clock; omega
      simp only [mkFns]
      rw [evaluateApp_unary_timeout body env x state maxApp zero]
    | cons name names =>
      simp only [mkFns]
      by_cases zero : state.clock = 0
      · rw [evaluateApp_unary_timeout (.fn name none none 1 (mkFns names body)) env x state maxApp zero]
      · have clockOne : 1 ≤ state.clock := by omega
        have tailClock : (ClosSem.decClock 1 state).clock ≤ names.length := by
          simp [ClosSem.decClock] at *; omega
        have tailLength : names.length < args.length := by simp at lengths; omega
        have tailMax : 1 ≤ (ClosSem.decClock 1 state).maxApp := by
          simpa [ClosSem.decClock] using maxApp
        rw [evaluateApp_nestedFn name (mkFns names body) env x state maxApp clockOne]
        simp only
        rw [ih names (ClosSem.decClock 1 state) (x :: env) tailClock tailLength tailMax]
        simp [ClosSem.decClock]

/-- When the nested functions and final unary closure are fully applied,
evaluate the body with the consumed arguments and continue with the remainder. -/
@[hol "cakeml/compiler/backend/proofs/clos_mtiProofScript.sml" "evaluate_apps_Clos_long"
  (fmap_as_finite_support := [refs, code])]
theorem evaluateApps_nestedFns_long {C F : Type} (args : List ClosSem.Value)
    (names : List Flapjack.Basis.Pure.MlString.MlString) (state : ClosSem.State C F)
    (body : ClosLang.Exp) (env : List ClosSem.Value)
    (premises : names.length < state.clock ∧ names.length < args.length ∧ 1 ≤ state.maxApp) :
    evaluateApps (.closure none [] env 1 (mkFns names body)) args state =
      match ClosSem.evaluate [body]
          ((args.reverse.take (1 + names.length)).reverse ++ env)
          (ClosSem.decClock (1 + names.length) state) with
      | (.val [value], next) => evaluateApps value ((args.reverse.drop (1 + names.length)).reverse) next
      | result => result := by
  obtain ⟨clock, lengths, maxApp⟩ := premises
  induction args using List.reverseRecOn generalizing names env state with
  | nil => simp at lengths
  | append_singleton args x ih =>
    rw [evaluateApps_snoc]
    cases names with
    | nil =>
      have clockOne : 1 ≤ state.clock := by simp at clock; omega
      simp only [mkFns]
      rw [evaluateApp_unary body env x state maxApp clockOne]
      simp [List.reverse_append]
    | cons name names =>
      have clockOne : 1 ≤ state.clock := by simp at clock; omega
      have tailClock : names.length < (ClosSem.decClock 1 state).clock := by
        simp [ClosSem.decClock] at *; omega
      have tailLength : names.length < args.length := by simp at lengths; omega
      have tailMax : 1 ≤ (ClosSem.decClock 1 state).maxApp := by
        simpa [ClosSem.decClock] using maxApp
      simp only [mkFns]
      rw [evaluateApp_nestedFn name (mkFns names body) env x state maxApp clockOne]
      simp only
      rw [ih names (ClosSem.decClock 1 state) (x :: env) tailClock tailLength tailMax]
      simp [List.reverse_append, ClosSem.decClock, Nat.sub_sub, Nat.add_comm]
      simp [show 1 + (names.length + 1) = Nat.succ (names.length + 1) by omega,
        List.append_assoc]

/-- Reconstructed applications propagate an error from their argument list.
This is a Lean-side evaluator property; HOL correspondence is still pending. -/
theorem mkApps_argument_error {C F : Type} (traces : List BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state next : ClosSem.State C F)
    (error : ErrorResult ClosSem.Value) (function : ClosLang.Exp)
    (run : ClosSem.evaluate args env state = (.err error, next))
    (lengthEq : args.length = traces.length) :
    ClosSem.evaluate [mkApps function (traces.zip args)] env state = (.err error, next) := by
  induction traces generalizing args state with
  | nil =>
    cases args with
    | nil => simp [ClosSem.evaluate] at run
    | cons x xs => simp at lengthEq
  | cons trace traces ih =>
    cases args with
    | nil => simp at lengthEq
    | cons arg args =>
      have lengths : args.length = traces.length := by simpa using lengthEq
      cases first : ClosSem.evaluate [arg] env state with
      | mk result middle =>
        cases result with
        | err firstError =>
          have full := ClosProps.evaluate_cons_error arg args env state middle firstError first
          rw [full] at run
          cases run
          simpa [mkApps] using unaryApp_arg_error trace (mkApps function (traces.zip args)) arg env state next error first
        | val values =>
          obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value arg env state middle values first
          have full := ClosProps.evaluate_cons_value arg args env state middle value first
          cases tail : ClosSem.evaluate args env middle with
          | mk tailResult last =>
            rw [full, tail] at run
            cases tailResult with
            | val values => simp at run
            | err tailError =>
              simp only at run
              cases run
              have nested := ih args middle tail lengths
              simpa [mkApps] using unaryApp_function_error trace (mkApps function (traces.zip args)) arg env state middle next value error first nested

/-- After the argument list succeeds, an error in the reconstructed head
function propagates through all the unary applications. -/
theorem mkApps_function_error {C F : Type} (traces : List BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state middle next : ClosSem.State C F)
    (values : List ClosSem.Value) (error : ErrorResult ClosSem.Value) (function : ClosLang.Exp)
    (functionRun : ClosSem.evaluate [function] env middle = (.err error, next))
    (argsRun : ClosSem.evaluate args env state = (.val values, middle))
    (lengthEq : args.length = traces.length) :
    ClosSem.evaluate [mkApps function (traces.zip args)] env state = (.err error, next) := by
  induction traces generalizing args state values with
  | nil =>
    cases args with
    | nil =>
      simp [ClosSem.evaluate] at argsRun
      obtain ⟨_, rfl⟩ := argsRun
      simpa [mkApps] using functionRun
    | cons x xs => simp at lengthEq
  | cons trace traces ih =>
    cases args with
    | nil => simp at lengthEq
    | cons arg args =>
      have lengths : args.length = traces.length := by simpa using lengthEq
      cases first : ClosSem.evaluate [arg] env state with
      | mk result afterFirst =>
        cases result with
        | err firstError =>
          have full := ClosProps.evaluate_cons_error arg args env state afterFirst firstError first
          rw [full] at argsRun
          simp at argsRun
        | val firstValues =>
          obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value arg env state afterFirst firstValues first
          have full := ClosProps.evaluate_cons_value arg args env state afterFirst value first
          cases tail : ClosSem.evaluate args env afterFirst with
          | mk tailResult last =>
            rw [full, tail] at argsRun
            cases tailResult with
            | err tailError => simp at argsRun
            | val tailValues =>
              simp only at argsRun
              cases argsRun
              have nested := ih args afterFirst tailValues tail lengths
              simpa [mkApps] using unaryApp_function_error trace (mkApps function (traces.zip args)) arg
                env state afterFirst next value error first nested

/-- Successful head and argument evaluation agrees with applying the
collected values through the corresponding nested unary applications. -/
theorem mkApps_success {C F : Type} (traces : List BackendCommon.Tra)
    (args : List ClosLang.Exp) (env : List ClosSem.Value) (state middle next : ClosSem.State C F)
    (values : List ClosSem.Value) (fn : ClosSem.Value) (function : ClosLang.Exp)
    (functionRun : ClosSem.evaluate [function] env middle = (.val [fn], next))
    (argsRun : ClosSem.evaluate args env state = (.val values, middle))
    (lengthEq : args.length = traces.length) :
    ClosSem.evaluate [mkApps function (traces.zip args)] env state = evaluateApps fn values next := by
  induction traces generalizing args state values with
  | nil =>
    cases args with
    | nil =>
      simp [ClosSem.evaluate] at argsRun
      obtain ⟨rfl, rfl⟩ := argsRun
      simpa [mkApps, evaluateApps] using functionRun
    | cons x xs => simp at lengthEq
  | cons trace traces ih =>
    cases args with
    | nil => simp at lengthEq
    | cons arg args =>
      have lengths : args.length = traces.length := by simpa using lengthEq
      cases first : ClosSem.evaluate [arg] env state with
      | mk result afterFirst =>
        cases result with
        | err firstError =>
          have full := ClosProps.evaluate_cons_error arg args env state afterFirst firstError first
          rw [full] at argsRun
          simp at argsRun
        | val firstValues =>
          obtain ⟨value, rfl⟩ := ClosSem.evaluate_singleton_value arg env state afterFirst firstValues first
          have full := ClosProps.evaluate_cons_value arg args env state afterFirst value first
          cases tail : ClosSem.evaluate args env afterFirst with
          | mk tailResult last =>
            rw [full, tail] at argsRun
            cases tailResult with
            | err tailError => simp at argsRun
            | val tailValues =>
              simp only at argsRun
              cases argsRun
              have nested := ih args afterFirst tailValues tail lengths
              cases applied : evaluateApps fn tailValues next with
              | mk appliedResult afterApply =>
                rw [applied] at nested
                cases appliedResult with
                | err error =>
                  have run := unaryApp_function_error trace (mkApps function (traces.zip args)) arg
                    env state afterFirst afterApply value error first nested
                  simpa [mkApps, evaluateApps, applied] using run
                | val appliedValues =>
                  obtain ⟨appliedValue, rfl⟩ := evaluateApps_singleton fn tailValues next afterApply appliedValues applied
                  have run := unaryApp_success trace (mkApps function (traces.zip args)) arg
                    env state afterFirst afterApply value appliedValue first nested
                  simpa [mkApps, evaluateApps, applied] using run

end Flapjack.Compiler.Backend.ClosMti

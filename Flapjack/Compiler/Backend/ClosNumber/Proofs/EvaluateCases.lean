import Flapjack.Compiler.Backend.ClosNumber.Proofs.StateRelation
import Flapjack.Compiler.Backend.ClosNumber.Proofs.ClosureApplication
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallConst

/-! Initial cases of the closure-numbering evaluator simulation. -/
namespace Flapjack.Compiler.Backend.ClosNumber
open Flapjack.SemanticPrimitivesHOL (Result)
open Flapjack.Compiler.Backend.ClosSem

/-- Result relation for numbering: returned lists and raised values are
related, and abort reasons are unchanged. -/
def ResultRel (maxApp : Nat) : Result (List Value) Value → Result (List Value) Value → Prop
  | .val left, .val right => List.Forall₂ (ValueRel maxApp) left right
  | .err (.raise left), .err (.raise right) => ValueRel maxApp left right
  | .err (.abort left), .err (.abort right) => left = right
  | _, _ => False

/-- One list case of the intended evaluator simulation. This relation uses
the proof-side states and evaluator and is not yet a reviewed HOL port. -/
def EvalSimulation {C F : Type} (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env nextEnv : List Value) (source : State (Nat × C) F) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F) (start : Nat),
    evaluate expressions env source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) →
    ¬ ClosProps.containsAppSome source.maxApp expressions →
    List.Forall₂ (ValueRel source.maxApp) env nextEnv → StateRel source target →
    ∃ targetResult targetNext,
      evaluate (renumberList start expressions).2 nextEnv target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext

/-- Induction hypothesis for indirect closure application. This is proof-side
    infrastructure, pending the complete evaluator correspondence review. -/
def AppSimulation {C F : Type} : Prop :=
  ∀ (function nextFunction : Value) (args nextArgs : List Value)
    (source : State (Nat × C) F) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F),
    evaluateApp none function args source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) →
    ValueRel source.maxApp function nextFunction →
    List.Forall₂ (ValueRel source.maxApp) args nextArgs → StateRel source target →
    ∃ targetResult targetNext,
      evaluateApp none nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext

/-- Application simulations restricted to strictly smaller argument lists.
    This supplies the well-founded recursive hypothesis for over-application. -/
def AppSimulationBelow {C F : Type} (bound : Nat) : Prop :=
  ∀ (function nextFunction : Value) (args nextArgs : List Value)
    (source : State (Nat × C) F) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F),
    args.length < bound →
    evaluateApp none function args source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) →
    ValueRel source.maxApp function nextFunction →
    List.Forall₂ (ValueRel source.maxApp) args nextArgs → StateRel source target →
    ∃ targetResult targetNext,
      evaluateApp none nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext

/-- Applying no arguments returns the related closure without changing state. -/
theorem evaluateApp_empty {C F : Type} (function nextFunction : Value)
    (source : State (Nat × C) F) (target : State C F)
    (related : ValueRel source.maxApp function nextFunction) (stateRel : StateRel source target) :
    ∃ targetResult targetNext,
      evaluateApp none nextFunction [] target = (targetResult, targetNext) ∧
      ResultRel source.maxApp (evaluateApp none function [] source).1 targetResult ∧
      StateRel (evaluateApp none function [] source).2 targetNext := by
  refine ⟨.val [nextFunction], target, ?_, ?_, ?_⟩
  · rw [evaluateApp]
  · simpa [evaluateApp, ResultRel] using List.Forall₂.cons related .nil
  · simpa [evaluateApp] using stateRel

/-- A partial indirect application returns a related partial closure, or the
    same timeout with both clocks set to zero. -/
theorem evaluateApp_partial {C F : Type} (function nextFunction first : Value)
    (rest nextArgs : List Value) (source : State (Nat × C) F) (target : State C F)
    (partialValue : Value) (result : Result (List Value) Value) (sourceNext : State (Nat × C) F)
    (run : evaluateApp none function (first :: rest) source = (result, sourceNext))
    (found : destClosure source.maxApp none function (first :: rest) = some (.partialApp partialValue))
    (related : ValueRel source.maxApp function nextFunction)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) (first :: rest) nextArgs)
    (stateRel : StateRel source target) :
    ∃ targetResult targetNext, evaluateApp none nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨nextPartial, nextFound, partialRel⟩ :=
    destClosure_related_partial source.maxApp function nextFunction (first :: rest) nextArgs partialValue
      related argsRel found
  have maxEq : source.maxApp = target.maxApp := (stateRel_clock_maxApp stateRel).2
  have clockEq : source.clock = target.clock := stateRel.1
  have lengthEq : (first :: rest).length = nextArgs.length := argsRel.length_eq
  cases argsRel with
  | cons head tail =>
    rename_i nextFirst nextRest
    have targetFound : destClosure target.maxApp none nextFunction (nextFirst :: nextRest) =
        some (.partialApp nextPartial) := by simpa [← maxEq] using nextFound
    by_cases insufficient : source.clock < (first :: rest).length
    · have targetInsufficient : target.clock < (nextFirst :: nextRest).length := by
        simpa [← clockEq, ← lengthEq] using insufficient
      rw [evaluateApp, found] at run
      dsimp only at run
      rw [if_pos insufficient] at run
      cases run
      refine ⟨.err (.abort .timeoutError), { target with clock := 0 }, ?_, rfl, ?_⟩
      · rw [evaluateApp, targetFound]
        dsimp only
        rw [if_pos targetInsufficient]
        rfl
      · exact stateRel_withClock 0 stateRel
    · have targetEnough : ¬ target.clock < (nextFirst :: nextRest).length := by
        simpa [← clockEq, ← lengthEq] using insufficient
      rw [evaluateApp, found] at run
      dsimp only at run
      rw [if_neg insufficient] at run
      cases run
      refine ⟨.val [nextPartial], decClock (nextFirst :: nextRest).length target, ?_, ?_, ?_⟩
      · rw [evaluateApp, targetFound]
        dsimp only
        rw [if_neg targetEnough]
      · exact .cons partialRel .nil
      · simpa [decClock, ← clockEq, ← lengthEq] using
          stateRel_withClock (source.clock - (first :: rest).length) stateRel

/-- A rejected indirect application is excluded by the original theorem's
    non-type-error premise. -/
theorem evaluateApp_rejected {C F : Type} (function first : Value) (rest : List Value)
    (source : State (Nat × C) F) (result : Result (List Value) Value)
    (sourceNext : State (Nat × C) F)
    (run : evaluateApp none function (first :: rest) source = (result, sourceNext))
    (rejected : destClosure source.maxApp none function (first :: rest) = none)
    (noType : result ≠ .err (.abort .typeError)) : False := by
  rw [evaluateApp, rejected] at run
  dsimp only at run
  cases run
  exact noType rfl

/-- Full applications that exhaust the clock time out in both related
    executions, even when their remaining argument lists differ in values. -/
theorem evaluateApp_full_timeout {C F : Type} (function nextFunction first : Value)
    (rest nextArgs : List Value) (source : State (Nat × C) F) (target : State C F)
    (body : ClosLang.Exp) (bodyEnv remaining : List Value)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F)
    (run : evaluateApp none function (first :: rest) source = (result, sourceNext))
    (found : destClosure source.maxApp none function (first :: rest) = some (.fullApp body bodyEnv remaining))
    (insufficient : source.clock < (first :: rest).length - remaining.length)
    (related : ValueRel source.maxApp function nextFunction)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) (first :: rest) nextArgs)
    (stateRel : StateRel source target) :
    ∃ targetResult targetNext, evaluateApp none nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨start, nextEnv, nextRemaining, nextFound, envRel, remainingRel, bodySafe⟩ :=
    destClosure_related_full source.maxApp function nextFunction (first :: rest) nextArgs
      body bodyEnv remaining related argsRel found
  have maxEq : source.maxApp = target.maxApp := (stateRel_clock_maxApp stateRel).2
  have clockEq : source.clock = target.clock := stateRel.1
  have lengthEq : (first :: rest).length = nextArgs.length := argsRel.length_eq
  have remainingEq : remaining.length = nextRemaining.length := remainingRel.length_eq
  cases argsRel with
  | cons head tail =>
    rename_i nextFirst nextRest
    have targetFound : destClosure target.maxApp none nextFunction (nextFirst :: nextRest) =
        some (.fullApp (renumber start body).2 nextEnv nextRemaining) := by simpa [← maxEq] using nextFound
    have targetInsufficient : target.clock < (nextFirst :: nextRest).length - nextRemaining.length := by
      simpa [← clockEq, ← lengthEq, ← remainingEq] using insufficient
    rw [evaluateApp, found] at run
    dsimp only at run
    rw [if_pos insufficient] at run
    cases run
    refine ⟨.err (.abort .timeoutError), { target with clock := 0 }, ?_, rfl, stateRel_withClock 0 stateRel⟩
    rw [evaluateApp, targetFound]
    dsimp only
    rw [if_pos targetInsufficient]
    rfl

/-- A full application with enough clock composes the numbered body simulation
    with the remaining-argument application hypothesis. The two hypotheses
    are factored prerequisites for the eventual mutual induction. -/
theorem evaluateApp_full {C F : Type} (function nextFunction first : Value)
    (rest nextArgs : List Value) (source : State (Nat × C) F) (target : State C F)
    (body : ClosLang.Exp) (bodyEnv remaining : List Value)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F)
    (run : evaluateApp none function (first :: rest) source = (result, sourceNext))
    (found : destClosure source.maxApp none function (first :: rest) = some (.fullApp body bodyEnv remaining))
    (enough : ¬ source.clock < (first :: rest).length - remaining.length)
    (noType : result ≠ .err (.abort .typeError))
    (related : ValueRel source.maxApp function nextFunction)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) (first :: rest) nextArgs)
    (stateRel : StateRel source target)
    (bodyIH : EvalSimulation (C := C) (F := F) [body])
    (applicationIH : AppSimulationBelow (C := C) (F := F) (first :: rest).length) :
    ∃ targetResult targetNext, evaluateApp none nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨start, nextEnv, nextRemaining, nextFound, envRel, remainingRel, bodySafe⟩ :=
    destClosure_related_full source.maxApp function nextFunction (first :: rest) nextArgs
      body bodyEnv remaining related argsRel found
  have maxEq : source.maxApp = target.maxApp := (stateRel_clock_maxApp stateRel).2
  have clockEq : source.clock = target.clock := stateRel.1
  have lengthEq : (first :: rest).length = nextArgs.length := argsRel.length_eq
  have remainingEq : remaining.length = nextRemaining.length := remainingRel.length_eq
  cases argsRel with
  | cons head tail =>
    rename_i nextFirst nextRest
    let cost := (first :: rest).length - remaining.length
    have targetCost : (nextFirst :: nextRest).length - nextRemaining.length = cost := by
      simp [cost, ← lengthEq, ← remainingEq]
    have targetFound : destClosure target.maxApp none nextFunction (nextFirst :: nextRest) =
        some (.fullApp (renumber start body).2 nextEnv nextRemaining) := by simpa [← maxEq] using nextFound
    have targetEnough : ¬ target.clock < (nextFirst :: nextRest).length - nextRemaining.length := by
      rw [targetCost, ← clockEq]
      exact enough
    have startRel : StateRel (decClock cost source) (decClock cost target) := by
      simpa [decClock, ← clockEq] using stateRel_withClock (source.clock - cost) stateRel
    have bodyEnvRel : List.Forall₂ (ValueRel (decClock cost source).maxApp) bodyEnv nextEnv := envRel
    have bodySafe' : ¬ ClosProps.containsAppSome (decClock cost source).maxApp [body] := bodySafe
    rw [evaluateApp, found] at run
    dsimp only at run
    rw [if_neg enough, fixClock_evaluate] at run
    cases bodyRun : evaluate [body] bodyEnv (decClock cost source) with
    | mk bodyResult last =>
      have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
        intro bad
        subst bodyResult
        rw [bodyRun] at run
        cases run
        exact noType rfl
      obtain ⟨targetBodyResult, targetLast, targetBodyRun, bodyRel, lastRel⟩ :=
        bodyIH bodyEnv nextEnv (decClock cost source) (decClock cost target)
          bodyResult last start bodyRun bodyNoType bodySafe' bodyEnvRel startRel
      cases bodyResult with
      | err error =>
        rw [bodyRun] at run
        cases run
        cases targetBodyResult with
        | val values => cases error <;> simp [ResultRel] at bodyRel
        | err targetError =>
          refine ⟨.err targetError, targetLast, ?_, bodyRel, lastRel⟩
          rw [evaluateApp, targetFound]
          dsimp only
          rw [if_neg targetEnough, targetCost, fixClock_evaluate]
          simp only [renumberList] at targetBodyRun
          rw [targetBodyRun]
      | val values =>
        have length := (evaluate_length (C := Nat × C) (F := F)).1 [body] bodyEnv
          (decClock cost source) last values bodyRun
        cases values with
        | nil => simp at length
        | cons value tail =>
          cases tail with
          | cons value' tail => simp at length
          | nil =>
            cases targetBodyResult with
            | err error => cases error <;> simp [ResultRel] at bodyRel
            | val targetValues =>
              cases bodyRel with
              | cons valueRel tailRel =>
                cases tailRel
                rename_i targetValue
                have lastMax : last.maxApp = source.maxApp := by
                  have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 [body] bodyEnv (decClock cost source)
                  rw [bodyRun] at h
                  exact h
                have appRun : evaluateApp none value remaining last = (result, sourceNext) := by
                  rw [bodyRun] at run
                  exact run
                obtain ⟨targetResult, targetNext, targetAppRun, resultRel, nextRel⟩ :=
                  applicationIH value targetValue remaining nextRemaining last targetLast result sourceNext
                    (destClosure_full_remaining_lt _ _ _ _ _ _ _ found) appRun noType (by simpa [lastMax, decClock] using valueRel)
                    (by simpa [lastMax] using remainingRel) lastRel
                refine ⟨targetResult, targetNext, ?_, ?_, nextRel⟩
                · rw [evaluateApp, targetFound]
                  dsimp only
                  rw [if_neg targetEnough, targetCost, fixClock_evaluate]
                  simp only [renumberList] at targetBodyRun
                  rw [targetBodyRun]
                  exact targetAppRun
                · simpa [lastMax] using resultRel

/-- Indirect application simulation follows by induction on the argument
    count, assuming simulations of all closure bodies. The body assumption is
    a remaining mutual-evaluator obligation, not an established HOL theorem. -/
theorem appSimulation_of_bodySimulations {C F : Type}
    (bodyIH : ∀ body, EvalSimulation (C := C) (F := F) [body]) :
    AppSimulation (C := C) (F := F) := by
  have bounded : ∀ bound, AppSimulationBelow (C := C) (F := F) bound := by
    intro bound
    induction bound using Nat.strong_induction_on with
    | h bound ih =>
      intro function nextFunction args nextArgs source target result sourceNext smaller run noType related argsRel stateRel
      cases args with
      | nil =>
        cases argsRel
        rw [evaluateApp] at run
        cases run
        simpa [evaluateApp] using evaluateApp_empty function nextFunction source target related stateRel
      | cons first rest =>
        cases found : destClosure source.maxApp none function (first :: rest) with
        | none => exact False.elim (evaluateApp_rejected function first rest source result sourceNext run found noType)
        | some kind =>
          cases kind with
          | partialApp partialValue =>
            exact evaluateApp_partial function nextFunction first rest nextArgs source target partialValue
              result sourceNext run found related argsRel stateRel
          | fullApp body bodyEnv remaining =>
            by_cases insufficient : source.clock < (first :: rest).length - remaining.length
            · exact evaluateApp_full_timeout function nextFunction first rest nextArgs source target body bodyEnv remaining
                result sourceNext run found insufficient related argsRel stateRel
            · exact evaluateApp_full function nextFunction first rest nextArgs source target body bodyEnv remaining
                result sourceNext run found insufficient noType related argsRel stateRel (bodyIH body)
                  (ih (first :: rest).length smaller)
  intro function nextFunction args nextArgs source target result sourceNext run noType related argsRel stateRel
  exact bounded (args.length + 1) function nextFunction args nextArgs source target result sourceNext
    (Nat.lt_succ_self _) run noType related argsRel stateRel

/-- An environment lookup preserves a pointwise relation. -/
theorem related_lookup {α β : Type} {relation : α → β → Prop} {left : List α} {right : List β}
    (related : List.Forall₂ relation left right) (index : Nat) (value : α)
    (found : left[index]? = some value) :
    ∃ target, right[index]? = some target ∧ relation value target := by
  induction related generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst value
      exact ⟨_, rfl, head⟩
    | succ index =>
      simp only [List.getElem?_cons_succ] at found ⊢
      exact ih index found

/-- Selecting captured environment slots preserves the value relation. -/
theorem related_lookupVars (maxApp : Nat) (indices : List Nat) (env nextEnv values : List Value)
    (envRel : List.Forall₂ (ValueRel maxApp) env nextEnv)
    (found : lookupVars indices env = some values) :
    ∃ nextValues, lookupVars indices nextEnv = some nextValues ∧
      List.Forall₂ (ValueRel maxApp) values nextValues := by
  induction indices generalizing values with
  | nil =>
    simp [lookupVars] at found
    subst values
    exact ⟨[], rfl, .nil⟩
  | cons index rest ih =>
    cases head : env[index]? with
    | none => simp [lookupVars, head] at found
    | some value =>
      cases tail : lookupVars rest env with
      | none => simp [lookupVars, head, tail] at found
      | some remaining =>
        simp [lookupVars, head, tail] at found
        subst values
        obtain ⟨nextValue, nextHead, valueRel⟩ := related_lookup envRel index value head
        obtain ⟨nextRemaining, nextTail, restRel⟩ := ih remaining tail
        exact ⟨nextValue :: nextRemaining, by simp [lookupVars, nextHead, nextTail], .cons valueRel restRel⟩

/-- Optional closure capture selects related environments in the same order. -/
theorem related_capture (maxApp : Nat) (selected : Option (List Nat)) (env nextEnv values : List Value)
    (envRel : List.Forall₂ (ValueRel maxApp) env nextEnv)
    (found : (match selected with | none => some env | some names => lookupVars names env) = some values) :
    ∃ nextValues, (match selected with | none => some nextEnv | some names => lookupVars names nextEnv) =
      some nextValues ∧ List.Forall₂ (ValueRel maxApp) values nextValues := by
  cases selected with
  | none =>
    simp at found
    subst values
    exact ⟨nextEnv, rfl, envRel⟩
  | some names => exact related_lookupVars maxApp names env nextEnv values envRel found

/-- Numbering the empty expression list preserves evaluation. -/
theorem evaluate_nil {C F : Type} : EvalSimulation (C := C) (F := F) [] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨.val [], target, by simp [renumberList, evaluate], .nil, stateRel⟩

/-- The variable case of numbering correctness, with the original non-type-
error condition and related environments and states. -/
theorem evaluate_var {C F : Type} (trace : BackendCommon.Tra) (index : Nat) :
    EvalSimulation (C := C) (F := F) [.var trace index] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  cases found : env[index]? with
  | none =>
    simp [evaluate, found] at run
    exact False.elim (noType run.1.symm)
  | some value =>
    simp [evaluate, found] at run
    obtain ⟨targetValue, targetFound, valueRel⟩ := related_lookup envRel index value found
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨.val [targetValue], target, ?_, ?_, stateRel⟩
    · simp [renumberList, renumber, evaluate, targetFound]
    · exact List.Forall₂.cons valueRel .nil

/-- Creating an ordinary closure preserves its captured environment and relates
the original body to its numbered form. -/
theorem evaluate_fn {C F : Type} (name : Flapjack.Basis.Pure.MlString.MlString)
    (location : Option Nat) (selected : Option (List Nat)) (arity : Nat) (body : ClosLang.Exp) :
    EvalSimulation (C := C) (F := F) [.fn name location selected arity body] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have maxEq : source.maxApp = target.maxApp := (stateRel_clock_maxApp stateRel).2
  have bodySafe : ¬ ClosProps.containsAppSome source.maxApp [body] := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  cases selected with
  | none =>
    by_cases arityOk : arity ≤ source.maxApp ∧ arity ≠ 0
    · simp [evaluate, arityOk] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨.val [.closure (some (renumber start body).1) [] nextEnv arity (renumber start body).2], target, ?_, ?_, stateRel⟩
      · simp [renumberList, renumber, evaluate, ← maxEq, arityOk]
      · exact List.Forall₂.cons (.closure location (some (renumber start body).1) [] [] env nextEnv
          arity start body _ envRel .nil bodySafe rfl) .nil
    · simp [evaluate, arityOk] at run
      exact False.elim (noType run.1.symm)
  | some names =>
    by_cases arityOk : arity ≤ source.maxApp ∧ arity ≠ 0
    · cases capture : lookupVars names env with
      | none =>
        simp [evaluate, arityOk, capture] at run
        exact False.elim (noType run.1.symm)
      | some values =>
        obtain ⟨nextValues, targetCapture, capturedRel⟩ := related_lookupVars source.maxApp names env nextEnv values envRel capture
        simp [evaluate, arityOk, capture] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨.val [.closure (some (renumber start body).1) [] nextValues arity (renumber start body).2], target, ?_, ?_, stateRel⟩
        · simp [renumberList, renumber, evaluate, ← maxEq, arityOk, targetCapture]
        · exact List.Forall₂.cons (.closure location (some (renumber start body).1) [] [] values nextValues
            arity start body _ capturedRel .nil bodySafe rfl) .nil
    · simp [evaluate, arityOk] at run
      exact False.elim (noType run.1.symm)

/-- The tick case of numbering correctness, assuming the induction hypothesis
for its body. Both evaluators decrement the same related clock. -/
theorem evaluate_tick {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (bodyIH : EvalSimulation (C := C) (F := F) [body]) :
    EvalSimulation (C := C) (F := F) [.tick trace body] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have bodySafe : ¬ ClosProps.containsAppSome source.maxApp [body] := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by rw [← stateRel.1]; exact zero
    simp [evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨.err (.abort .timeoutError), target, ?_, rfl, stateRel⟩
    simp [renumberList, renumber, evaluate, targetZero]
  · have targetNonzero : target.clock ≠ 0 := by rw [← stateRel.1]; exact zero
    have clocks : StateRel (decClock 1 source) (decClock 1 target) := by
      simpa [decClock, ← stateRel.1] using stateRel_withClock (source.clock - 1) stateRel
    have bodyRun : evaluate [body] env (decClock 1 source) = (result, sourceNext) := by
      simpa [evaluate, zero] using run
    obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
      bodyIH env nextEnv (decClock 1 source) (decClock 1 target) result sourceNext start
        bodyRun noType bodySafe envRel clocks
    refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
    simpa [renumberList, renumber, evaluate, targetNonzero] using targetRun

/-- Raising a value preserves the numbering relation, assuming the body
simulation. The evaluator's singleton-result theorem supplies the raised value. -/
theorem evaluate_raise {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (bodyIH : EvalSimulation (C := C) (F := F) [body]) :
    EvalSimulation (C := C) (F := F) [.raise trace body] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have bodySafe : ¬ ClosProps.containsAppSome source.maxApp [body] := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult bodyNext =>
    cases bodyResult with
    | err error =>
      simp [evaluate, bodyRun] at run
      obtain ⟨rfl, rfl⟩ := run
      have bodyNoType : Result.err error ≠ Result.err (.abort .typeError) := noType
      obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
        bodyIH env nextEnv source target (.err error) bodyNext start bodyRun bodyNoType bodySafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetNext, ?_, resultRel, nextRel⟩
        simp only [renumberList] at targetRun
        simp [renumberList, renumber, evaluate, targetRun]
    | val values =>
      have length := (evaluate_length (C := Nat × C) (F := F)).1 [body] env source bodyNext values bodyRun
      have bodyNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
        bodyIH env nextEnv source target (.val values) bodyNext start bodyRun bodyNoType bodySafe envRel stateRel
      cases values with
      | nil => simp at length
      | cons value tail =>
        cases tail with
        | cons first rest => simp at length
        | nil =>
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel restRel =>
              cases restRel
              simp [evaluate, bodyRun] at run
              obtain ⟨rfl, rfl⟩ := run
              refine ⟨.err (.raise _), targetNext, ?_, valueRel, nextRel⟩
              simp only [renumberList] at targetRun
              simp [renumberList, renumber, evaluate, targetRun]

/-- Sequencing preserves the simulation when the first expression and the
remaining nonempty list satisfy their respective induction hypotheses. -/
theorem evaluate_cons {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (firstIH : EvalSimulation (C := C) (F := F) [first])
    (restIH : EvalSimulation (C := C) (F := F) (second :: rest)) :
    EvalSimulation (C := C) (F := F) (first :: second :: rest) := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have safeParts : ¬ ClosProps.containsAppSomeExp source.maxApp first ∧
      ¬ ClosProps.containsAppSome source.maxApp (second :: rest) := by
    simpa only [ClosProps.containsAppSome, not_or] using safe
  have firstSafe : ¬ ClosProps.containsAppSome source.maxApp [first] := by
    simpa [ClosProps.containsAppSome] using safeParts.1
  have restSafe : ¬ ClosProps.containsAppSome source.maxApp (second :: rest) := safeParts.2
  cases firstRun : evaluate [first] env source with
  | mk firstResult middle =>
    cases firstResult with
    | err error =>
      have allRun := ClosProps.evaluate_cons_error first (second :: rest) env source middle error firstRun
      rw [allRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        firstIH env nextEnv source target (.err error) sourceNext start firstRun noType firstSafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList] at targetRun ⊢
        exact ClosProps.evaluate_cons_error _ _ _ _ _ _ targetRun
    | val values =>
      have length := (evaluate_length (C := Nat × C) (F := F)).1 [first] env source middle values firstRun
      cases values with
      | nil => simp at length
      | cons value tail =>
        cases tail with
        | cons value' tail => simp at length
        | nil =>
          have firstNoType : (Result.val [value] : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
          obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
            firstIH env nextEnv source target (.val [value]) middle start firstRun firstNoType firstSafe envRel stateRel
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel tailRel =>
              cases tailRel
              rename_i targetValue
              have maxEq : middle.maxApp = source.maxApp := by
                have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 [first] env source
                simpa [firstRun] using h
              have middleSafe : ¬ ClosProps.containsAppSome middle.maxApp (second :: rest) := by
                simpa [maxEq] using restSafe
              have middleEnv : List.Forall₂ (ValueRel middle.maxApp) env nextEnv := by
                simpa [maxEq] using envRel
              cases restRun : evaluate (second :: rest) env middle with
              | mk restResult last =>
                have allRun := ClosProps.evaluate_cons_value first (second :: rest) env source middle value firstRun
                rw [restRun] at allRun
                cases restResult with
                | err error =>
                  simp only at allRun
                  rw [allRun] at run
                  cases run
                  obtain ⟨targetRestResult, targetLast, targetRestRun, restRel, lastRel⟩ :=
                    restIH env nextEnv middle targetMiddle (.err error) sourceNext (renumber start first).1
                      restRun noType middleSafe middleEnv middleRel
                  cases targetRestResult with
                  | val values => cases error <;> simp [ResultRel] at restRel
                  | err targetError =>
                    refine ⟨.err targetError, targetLast, ?_, ?_, lastRel⟩
                    · simp only [renumberList] at targetRun targetRestRun ⊢
                      rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ targetRun, targetRestRun]
                    · simpa [maxEq] using restRel
                | val values =>
                  simp only at allRun
                  rw [allRun] at run
                  cases run
                  have restNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
                  obtain ⟨targetRestResult, targetLast, targetRestRun, restRel, lastRel⟩ :=
                    restIH env nextEnv middle targetMiddle (.val values) sourceNext (renumber start first).1
                      restRun restNoType middleSafe middleEnv middleRel
                  cases targetRestResult with
                  | err error => cases error <;> simp [ResultRel] at restRel
                  | val targetValues =>
                    refine ⟨.val (targetValue :: targetValues), targetLast, ?_, ?_, lastRel⟩
                    · simp only [renumberList] at targetRun targetRestRun ⊢
                      rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ targetRun, targetRestRun]
                    · exact List.Forall₂.cons valueRel (by simpa [ResultRel, maxEq] using restRel)

/-- A let expression preserves evaluation when its bindings and body satisfy
    their simulations. The environment is extended in the evaluator's order. -/
theorem evaluate_let {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp)
    (bindingsIH : EvalSimulation (C := C) (F := F) bindings)
    (bodyIH : EvalSimulation (C := C) (F := F) [body]) :
    EvalSimulation (C := C) (F := F) [.let trace bindings body] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have safeParts : ¬ ClosProps.containsAppSomeExp source.maxApp body ∧
      ¬ ClosProps.containsAppSome source.maxApp bindings := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  have bodySafe : ¬ ClosProps.containsAppSome source.maxApp [body] := by
    simpa [ClosProps.containsAppSome] using safeParts.1
  cases bindingsRun : evaluate bindings env source with
  | mk bindingsResult middle =>
    cases bindingsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, bindingsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        bindingsIH env nextEnv source target (.err error) middle start bindingsRun
          noType safeParts.2 envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList, renumber]
        rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have bindingsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        bindingsIH env nextEnv source target (.val values) middle start bindingsRun
          bindingsNoType safeParts.2 envRel stateRel
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at resultRel
      | val targetValues =>
        have maxEq : middle.maxApp = source.maxApp := by
          have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 bindings env source
          simpa [bindingsRun] using h
        have bodySafe' : ¬ ClosProps.containsAppSome middle.maxApp [body] := by
          simpa [maxEq] using bodySafe
        have extended : List.Forall₂ (ValueRel middle.maxApp) (values ++ env) (targetValues ++ nextEnv) := by
          apply List.rel_append
          · simpa [ResultRel, maxEq] using resultRel
          · simpa [maxEq] using envRel
        have bodyRun : evaluate [body] (values ++ env) middle = (result, sourceNext) := by
          rw [evaluate, fixClock_evaluate, bindingsRun] at run
          exact run
        obtain ⟨targetBodyResult, targetLast, targetBodyRun, bodyRel, lastRel⟩ :=
          bodyIH (values ++ env) (targetValues ++ nextEnv) middle targetMiddle result sourceNext
            (renumberList start bindings).1 bodyRun noType bodySafe' extended middleRel
        refine ⟨targetBodyResult, targetLast, ?_, ?_, lastRel⟩
        · simp only [renumberList] at targetBodyRun
          simp only [renumberList, renumber]
          rw [evaluate, fixClock_evaluate, targetRun]
          exact targetBodyRun
        · simpa [maxEq] using bodyRel

/-- A handler preserves normal and abort results and evaluates related handlers
    with related raised values prepended to their environments. -/
theorem evaluate_handle {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp)
    (bodyIH : EvalSimulation (C := C) (F := F) [body])
    (handlerIH : EvalSimulation (C := C) (F := F) [handler]) :
    EvalSimulation (C := C) (F := F) [.handle trace body handler] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have safeParts : ¬ ClosProps.containsAppSomeExp source.maxApp body ∧
      ¬ ClosProps.containsAppSomeExp source.maxApp handler := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  have bodySafe : ¬ ClosProps.containsAppSome source.maxApp [body] := by
    simpa [ClosProps.containsAppSome] using safeParts.1
  have handlerSafe : ¬ ClosProps.containsAppSome source.maxApp [handler] := by
    simpa [ClosProps.containsAppSome] using safeParts.2
  cases bodyRun : evaluate [body] env source with
  | mk bodyResult middle =>
    have bodyNoType : bodyResult ≠ .err (.abort .typeError) := by
      intro bad
      subst bodyResult
      rw [evaluate, fixClock_evaluate, bodyRun] at run
      cases run
      exact noType rfl
    obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
      bodyIH env nextEnv source target bodyResult middle start bodyRun bodyNoType bodySafe envRel stateRel
    cases bodyResult with
    | val values =>
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at resultRel
      | val targetValues =>
        rw [evaluate, fixClock_evaluate, bodyRun] at run
        cases run
        refine ⟨.val targetValues, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList] at targetRun
        simp only [renumberList, renumber]
        rw [evaluate, fixClock_evaluate, targetRun]
    | err error =>
      cases error with
      | abort reason =>
        cases targetResult with
        | val values => simp [ResultRel] at resultRel
        | err targetError =>
          cases targetError with
          | raise value => simp [ResultRel] at resultRel
          | abort targetReason =>
            rw [evaluate, fixClock_evaluate, bodyRun] at run
            cases run
            refine ⟨.err (.abort targetReason), targetMiddle, ?_, resultRel, middleRel⟩
            simp only [renumberList] at targetRun
            simp only [renumberList, renumber]
            rw [evaluate, fixClock_evaluate, targetRun]
      | raise value =>
        cases targetResult with
        | val values => simp [ResultRel] at resultRel
        | err targetError =>
          cases targetError with
          | abort reason => simp [ResultRel] at resultRel
          | raise targetValue =>
            have maxEq : middle.maxApp = source.maxApp := by
              have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 [body] env source
              simpa [bodyRun] using h
            have handlerSafe' : ¬ ClosProps.containsAppSome middle.maxApp [handler] := by
              simpa [maxEq] using handlerSafe
            have extended : List.Forall₂ (ValueRel middle.maxApp) (value :: env) (targetValue :: nextEnv) := by
              apply List.Forall₂.cons
              · simpa [ResultRel, maxEq] using resultRel
              · simpa [maxEq] using envRel
            have handlerRun : evaluate [handler] (value :: env) middle = (result, sourceNext) := by
              rw [evaluate, fixClock_evaluate, bodyRun] at run
              exact run
            obtain ⟨targetHandlerResult, targetLast, targetHandlerRun, handlerRel, lastRel⟩ :=
              handlerIH (value :: env) (targetValue :: nextEnv) middle targetMiddle result sourceNext
                (renumber start body).1 handlerRun noType handlerSafe' extended middleRel
            refine ⟨targetHandlerResult, targetLast, ?_, ?_, lastRel⟩
            · simp only [renumberList] at targetRun targetHandlerRun
              simp only [renumberList, renumber]
              rw [evaluate, fixClock_evaluate, targetRun]
              exact targetHandlerRun
            · simpa [maxEq] using handlerRel

/-- Numbering preserves the evaluator's Boolean observation. -/
theorem valueRel_asBool {maxApp : Nat} {left right : Value}
    (related : ValueRel maxApp left right) : asBool left = asBool right := by
  cases related with
  | block tag left right entries =>
    cases entries with
    | nil => rfl
    | cons head tail => cases tag <;> simp [asBool]
  | number _ | word64 _ | byteVector _ | refPtr _ _ => rfl
  | closure => rfl
  | recclosure => rfl

/-- Conditionals follow the same branch after numbering, assuming the
    condition and both branches satisfy their simulations. -/
theorem evaluate_if {C F : Type} (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp)
    (conditionIH : EvalSimulation (C := C) (F := F) [condition])
    (yesIH : EvalSimulation (C := C) (F := F) [yes])
    (noIH : EvalSimulation (C := C) (F := F) [no]) :
    EvalSimulation (C := C) (F := F) [.ifThenElse trace condition yes no] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have safeParts : ¬ ClosProps.containsAppSomeExp source.maxApp condition ∧
      ¬ ClosProps.containsAppSomeExp source.maxApp yes ∧
      ¬ ClosProps.containsAppSomeExp source.maxApp no := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  have conditionSafe : ¬ ClosProps.containsAppSome source.maxApp [condition] := by
    simpa [ClosProps.containsAppSome] using safeParts.1
  have yesSafe : ¬ ClosProps.containsAppSome source.maxApp [yes] := by
    simpa [ClosProps.containsAppSome] using safeParts.2.1
  have noSafe : ¬ ClosProps.containsAppSome source.maxApp [no] := by
    simpa [ClosProps.containsAppSome] using safeParts.2.2
  cases conditionRun : evaluate [condition] env source with
  | mk conditionResult middle =>
    cases conditionResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, conditionRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        conditionIH env nextEnv source target (.err error) middle start conditionRun
          noType conditionSafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList] at targetRun
        simp only [renumberList, renumber]
        rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have length := (evaluate_length (C := Nat × C) (F := F)).1 [condition] env source middle values conditionRun
      cases values with
      | nil => simp at length
      | cons value tail =>
        cases tail with
        | cons value' tail => simp at length
        | nil =>
          have conditionNoType : (Result.val [value] : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
          obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
            conditionIH env nextEnv source target (.val [value]) middle start conditionRun
              conditionNoType conditionSafe envRel stateRel
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel tailRel =>
              cases tailRel
              rename_i targetValue
              have boolEq : asBool value = asBool targetValue := valueRel_asBool valueRel
              have maxEq : middle.maxApp = source.maxApp := by
                have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 [condition] env source
                simpa [conditionRun] using h
              have middleEnv : List.Forall₂ (ValueRel middle.maxApp) env nextEnv := by
                simpa [maxEq] using envRel
              cases decision : asBool value with
              | none =>
                rw [evaluate, fixClock_evaluate, conditionRun] at run
                simp [decision] at run
                exact False.elim (noType run.1.symm)
              | some flag =>
                have targetDecision : asBool targetValue = some flag := by rw [← boolEq]; exact decision
                cases flag with
                | false =>
                  have branchRun : evaluate [no] env middle = (result, sourceNext) := by
                    rw [evaluate, fixClock_evaluate, conditionRun] at run
                    simpa [decision] using run
                  obtain ⟨targetBranchResult, targetLast, targetBranchRun, branchRel, lastRel⟩ :=
                    noIH env nextEnv middle targetMiddle result sourceNext
                      (renumber (renumber start condition).1 yes).1 branchRun noType
                      (by simpa [maxEq] using noSafe) middleEnv middleRel
                  refine ⟨targetBranchResult, targetLast, ?_, ?_, lastRel⟩
                  · simp only [renumberList] at targetRun targetBranchRun
                    simp only [renumberList, renumber]
                    rw [evaluate, fixClock_evaluate, targetRun]
                    simpa [targetDecision] using targetBranchRun
                  · simpa [maxEq] using branchRel
                | true =>
                  have branchRun : evaluate [yes] env middle = (result, sourceNext) := by
                    rw [evaluate, fixClock_evaluate, conditionRun] at run
                    simpa [decision] using run
                  obtain ⟨targetBranchResult, targetLast, targetBranchRun, branchRel, lastRel⟩ :=
                    yesIH env nextEnv middle targetMiddle result sourceNext
                      (renumber start condition).1 branchRun noType
                      (by simpa [maxEq] using yesSafe) middleEnv middleRel
                  refine ⟨targetBranchResult, targetLast, ?_, ?_, lastRel⟩
                  · simp only [renumberList] at targetRun targetBranchRun
                    simp only [renumberList, renumber]
                    rw [evaluate, fixClock_evaluate, targetRun]
                    simpa [targetDecision] using targetBranchRun
                  · simpa [maxEq] using branchRel

/-- Recursive closure creation preserves the related environment and evaluates
    the numbered body under corresponding recursive function bundles. -/
theorem evaluate_letrec {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat))
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp)
    (bodyIH : EvalSimulation (C := C) (F := F) [body]) :
    EvalSimulation (C := C) (F := F) [.letrec names location selected functions body] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have safeParts : ¬ ClosProps.containsAppSomeFuns source.maxApp functions ∧
      ¬ ClosProps.containsAppSomeExp source.maxApp body := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  have funSafe : ¬ ClosProps.containsAppSome source.maxApp (functions.map Prod.snd) := by
    simpa [ClosProps.containsAppSomeFuns_eq_map] using safeParts.1
  have bodySafe : ¬ ClosProps.containsAppSome source.maxApp [body] := by
    simpa [ClosProps.containsAppSome] using safeParts.2
  have maxEq : source.maxApp = target.maxApp := (stateRel_clock_maxApp stateRel).2
  rw [evaluate.eq_def] at run
  by_cases arityOk : functions.all (fun (arity, _) => arity ≤ source.maxApp && arity != 0)
  · simp only [arityOk, ↓reduceIte] at run
    cases captured : (match selected with | none => some env | some indices => lookupVars indices env) with
    | none =>
      cases selected <;> simp_all
    | some values =>
      obtain ⟨nextValues, nextCaptured, capturedRel⟩ :=
        related_capture source.maxApp selected env nextEnv values envRel captured
      have recRel := numberedRecclosures_related source.maxApp start location
        (some (renumberFuns start functions).1) values nextValues functions capturedRel funSafe
      rw [← renumberFuns_eq_bundle] at recRel
      have extended := List.rel_append recRel envRel
      have bodyRun : evaluate [body]
          (((List.range functions.length).map (fun i => Value.recclosure location [] values functions i)) ++ env)
          source = (result, sourceNext) := by
        cases selected <;> simp_all
      obtain ⟨targetResult, targetNext, targetRun, resultRel, nextRel⟩ :=
        bodyIH _ _ source target result sourceNext
          ((renumberFuns start functions).1 + 2 * (renumberFuns start functions).2.length)
          bodyRun noType bodySafe extended stateRel
      refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
      simp only [renumberList] at targetRun
      simp only [renumberList, renumber]
      rw [evaluate.eq_def]
      simp only [← maxEq, renumberFuns_all_arities, arityOk, ↓reduceIte]
      cases selected <;> simp_all
  · simp [arityOk] at run
    exact False.elim (noType run.1.symm)

/-- Indirect application composes argument and function evaluation with the
    application induction hypothesis. This factored hypothesis is universally
    quantified and must be discharged by the eventual mutual simulation. -/
theorem evaluate_app {C F : Type} (trace : BackendCommon.Tra)
    (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (argsIH : EvalSimulation (C := C) (F := F) args)
    (functionIH : EvalSimulation (C := C) (F := F) [function])
    (applicationIH : AppSimulation (C := C) (F := F)) :
    EvalSimulation (C := C) (F := F) [.app trace none function args] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have safeParts : args.length ≤ source.maxApp ∧
      ¬ ClosProps.containsAppSomeExp source.maxApp function ∧
      ¬ ClosProps.containsAppSome source.maxApp args := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp, not_or, Nat.not_lt] using safe
  have functionSafe : ¬ ClosProps.containsAppSome source.maxApp [function] := by
    simpa [ClosProps.containsAppSome] using safeParts.2.1
  cases args with
  | nil =>
    simp [evaluate] at run
    exact False.elim (noType run.1.symm)
  | cons first rest =>
    cases argsRun : evaluate (first :: rest) env source with
    | mk argsResult middle =>
      cases argsResult with
      | err error =>
        rw [evaluate, fixClock_evaluate, argsRun] at run
        cases run
        obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
          argsIH env nextEnv source target (.err error) middle (renumber start function).1 argsRun noType safeParts.2.2 envRel stateRel
        cases targetResult with
        | val values => cases error <;> simp [ResultRel] at resultRel
        | err targetError =>
          refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
          simp only [renumberList] at targetRun
          simp only [renumberList, renumber]
          rw [evaluate, fixClock_evaluate, targetRun]
          rfl
      | val values =>
        have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
        obtain ⟨targetArgsResult, targetMiddle, targetArgsRun, argsRel, middleRel⟩ :=
          argsIH env nextEnv source target (.val values) middle (renumber start function).1
            argsRun argsNoType safeParts.2.2 envRel stateRel
        cases targetArgsResult with
        | err error => cases error <;> simp [ResultRel] at argsRel
        | val targetValues =>
          have middleMax : middle.maxApp = source.maxApp := by
            have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 (first :: rest) env source
            simpa [argsRun] using h
          have middleEnv : List.Forall₂ (ValueRel middle.maxApp) env nextEnv := by
            simpa [middleMax] using envRel
          have middleSafe : ¬ ClosProps.containsAppSome middle.maxApp [function] := by
            simpa [middleMax] using functionSafe
          cases functionRun : evaluate [function] env middle with
          | mk functionResult last =>
            cases functionResult with
            | err error =>
              rw [evaluate, fixClock_evaluate, argsRun] at run
              simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
              rw [fixClock_evaluate, functionRun] at run
              cases run
              obtain ⟨targetResult, targetLast, targetRun, resultRel, lastRel⟩ :=
                functionIH env nextEnv middle targetMiddle (.err error) last start functionRun
                  noType middleSafe middleEnv middleRel
              cases targetResult with
              | val values => cases error <;> simp [ResultRel] at resultRel
              | err targetError =>
                refine ⟨.err targetError, targetLast, ?_, ?_, lastRel⟩
                · simp only [renumberList] at targetRun targetArgsRun
                  simp only [renumberList, renumber]
                  rw [evaluate, fixClock_evaluate, targetArgsRun]
                  simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                  rw [fixClock_evaluate, targetRun]
                · simpa [middleMax] using resultRel
            | val functions =>
              have length := (evaluate_length (C := Nat × C) (F := F)).1 [function] env middle last functions functionRun
              cases functions with
              | nil => simp at length
              | cons value tail =>
                cases tail with
                | cons value' tail => simp at length
                | nil =>
                  have functionNoType : (Result.val [value] : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
                  obtain ⟨targetFunctionResult, targetLast, targetFunctionRun, functionRel, lastRel⟩ :=
                    functionIH env nextEnv middle targetMiddle (.val [value]) last start functionRun
                      functionNoType middleSafe middleEnv middleRel
                  cases targetFunctionResult with
                  | err error => cases error <;> simp [ResultRel] at functionRel
                  | val targetFunctions =>
                    cases functionRel with
                    | cons valueRel tailRel =>
                      cases tailRel
                      rename_i targetValue
                      have lastMax : last.maxApp = middle.maxApp := by
                        have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 [function] env middle
                        simpa [functionRun] using h
                      have appRun : evaluateApp none value values last = (result, sourceNext) := by
                        rw [evaluate, fixClock_evaluate, argsRun] at run
                        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte] at run
                        rw [fixClock_evaluate, functionRun] at run
                        simpa using run
                      obtain ⟨targetResult, targetNext, targetAppRun, resultRel, nextRel⟩ :=
                        applicationIH value targetValue values targetValues last targetLast result sourceNext
                          appRun noType (by simpa [lastMax, middleMax] using valueRel)
                          (by simpa [ResultRel, lastMax, middleMax] using argsRel) lastRel
                      refine ⟨targetResult, targetNext, ?_, ?_, nextRel⟩
                      · simp only [renumberList] at targetArgsRun targetFunctionRun
                        simp only [renumberList, renumber]
                        rw [evaluate, fixClock_evaluate, targetArgsRun]
                        simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte]
                        rw [fixClock_evaluate, targetFunctionRun]
                        simpa using targetAppRun
                      · simpa [lastMax, middleMax] using resultRel

/-- Directly annotated applications cannot satisfy the simulation's source
    side condition; numbering correctness only considers indirect calls here. -/
theorem evaluate_app_some {C F : Type} (trace : BackendCommon.Tra) (location : Nat)
    (function : ClosLang.Exp) (args : List ClosLang.Exp) :
    EvalSimulation (C := C) (F := F) [.app trace (some location) function args] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  simp [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] at safe

/-- A direct call can only propagate an argument error under the numbering
    state relation: its source code map is empty after successful arguments. -/
theorem evaluate_call {C F : Type} (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (argsIH : EvalSimulation (C := C) (F := F) args) :
    EvalSimulation (C := C) (F := F) [.call trace ticks location args] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have argsSafe : ¬ ClosProps.containsAppSome source.maxApp args := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv source target (.err error) middle start argsRun noType argsSafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList, renumber]
        rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv source target (.val values) middle start argsRun argsNoType argsSafe envRel stateRel
      have emptyCode : middle.code = HolFiniteMapExact.empty := middleRel.2.2.2.2.2.2.2.2.1
      rw [evaluate, fixClock_evaluate, argsRun] at run
      simp [findCode, emptyCode, HolFiniteMapExact.empty] at run
      exact False.elim (noType run.1.symm)

/-- Integer operations inspect only numeric values, which numbering preserves. -/
theorem doIntApp_related (maxApp : Nat) (op : ClosLang.IntOp) {args nextArgs : List Value}
    (related : List.Forall₂ (ValueRel maxApp) args nextArgs) :
    doIntApp op args = doIntApp op nextArgs := by
  cases op <;> cases related with
  | nil => rfl
  | cons head tail =>
    cases head <;> cases tail <;> simp_all [doIntApp]
    all_goals
      rename_i head2 tail2
      cases head2 <;> cases tail2 <;> simp_all

/-- The Boolean values produced by integer comparisons relate to themselves. -/
theorem boolValue_related (maxApp : Nat) (value : Bool) :
    ValueRel maxApp (boolValue value) (boolValue value) := by
  cases value <;> exact .block _ [] [] .nil

/-- Integer primitives return only numbers or Boolean blocks, hence their
    successful result relates to itself. -/
theorem doIntApp_result_related (maxApp : Nat) (op : ClosLang.IntOp) (args : List Value) (value : Value)
    (run : doIntApp op args = some value) : ValueRel maxApp value value := by
  cases op <;> cases args <;> simp_all [doIntApp]
  all_goals try (subst value; exact .number _)
  all_goals
    rename_i head tail
    cases head <;> cases tail <;> try simp_all
    all_goals try (obtain ⟨_, rfl⟩ := run; exact boolValue_related _ _)
    all_goals
      rename_i head2 tail2
      cases head2 <;> cases tail2 <;> try simp_all
      all_goals try (subst value; exact .number _)
      all_goals try (subst value; exact boolValue_related _ _)
      all_goals try (obtain ⟨_, rfl⟩ := run; exact .number _)

/-- Integer primitive application preserves errors, related values and states. -/
theorem doApp_int_simulation {C F : Type} (op : ClosLang.IntOp) (args nextArgs : List Value)
    (source : State (Nat × C) F) (target : State C F)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) args nextArgs)
    (stateRel : StateRel source target) :
    match doApp (.intOp op) args source with
    | .err error => doApp (.intOp op) nextArgs target = .err error
    | .val (value, next) => ∃ nextValue nextState,
        doApp (.intOp op) nextArgs target = .val (nextValue, nextState) ∧
        ValueRel source.maxApp value nextValue ∧ StateRel next nextState := by
  have same := doIntApp_related source.maxApp op argsRel
  cases run : doIntApp op args with
  | none => simp [doApp, applyNumeric, ← same, run]
  | some value =>
    have valueRel := doIntApp_result_related source.maxApp op args value run
    simp [doApp, applyNumeric, ← same, run, valueRel, stateRel]

/-- Integer primitive expressions preserve evaluation after numbering, given
    the induction hypothesis for their argument expressions. -/
theorem evaluate_intOp {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.IntOp)
    (args : List ClosLang.Exp) (argsIH : EvalSimulation (C := C) (F := F) args) :
    EvalSimulation (C := C) (F := F) [.op trace (.intOp op) args] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have argsSafe : ¬ ClosProps.containsAppSome source.maxApp args := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv source target (.err error) middle start argsRun noType argsSafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList, renumber]
        rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, argsRel, middleRel⟩ :=
        argsIH env nextEnv source target (.val values) middle start argsRun argsNoType argsSafe envRel stateRel
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val nextValues =>
        have same := doIntApp_related source.maxApp op (List.rel_reverse argsRel)
        cases numeric : doIntApp op values.reverse with
        | none =>
          rw [evaluate, fixClock_evaluate, argsRun] at run
          simp [doApp, applyNumeric, numeric] at run
          exact False.elim (noType run.1.symm)
        | some value =>
          have valueRel := doIntApp_result_related source.maxApp op values.reverse value numeric
          rw [evaluate, fixClock_evaluate, argsRun] at run
          simp [doApp, applyNumeric, numeric] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨.val [value], targetMiddle, ?_, .cons valueRel .nil, middleRel⟩
          simp only [renumberList, renumber]
          rw [evaluate, fixClock_evaluate, targetRun]
          simp [doApp, applyNumeric, ← same, numeric]

/-- Related arguments give identical word-primitive observations, including
    the existing floating-point operations and their FpSemHOL assumptions. -/
theorem doWordApp_related (maxApp : Nat) (op : ClosLang.WordOp) {args nextArgs : List Value}
    (related : List.Forall₂ (ValueRel maxApp) args nextArgs) :
    doWordApp op args = doWordApp op nextArgs := by
  cases op <;> cases related with
  | nil => rfl
  | cons head tail =>
    cases head <;> cases tail <;> simp_all [doWordApp, doWordAppIntegral]
    all_goals
      rename_i head2 tail2
      cases head2 <;> cases tail2 <;> try simp_all
      all_goals
        rename_i head3 tail3
        cases head3 <;> cases tail3 <;> simp_all

/-- Successful word operations return scalar words, numbers, or Boolean
    values, each related to itself. -/
theorem doWordApp_result_related (maxApp : Nat) (op : ClosLang.WordOp) (args : List Value) (value : Value)
    (run : doWordApp op args = some value) : ValueRel maxApp value value := by
  cases op <;> cases args <;> simp_all [doWordApp, doWordAppIntegral]
  all_goals
    rename_i head tail
    cases head <;> cases tail <;> try simp_all
    all_goals try (subst value; exact .word64 _)
    all_goals try (subst value; exact .number _)
    all_goals
      repeat
        first
        | split at run
        | simp_all
        | subst value
        | exact .number _
        | exact .word64 _
        | exact boolValue_related _ _
    all_goals try simp_all
    all_goals simp [intToByte] at run
    all_goals split at run <;> simp_all
    all_goals try (split at run <;> simp_all)
    all_goals try (subst value; exact .number _)
    all_goals try (subst value; exact .word64 _)

/-- Word primitive expressions preserve evaluation after numbering, given
    the induction hypothesis for their argument expressions. -/
theorem evaluate_wordOp {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.WordOp)
    (args : List ClosLang.Exp) (argsIH : EvalSimulation (C := C) (F := F) args) :
    EvalSimulation (C := C) (F := F) [.op trace (.wordOp op) args] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have argsSafe : ¬ ClosProps.containsAppSome source.maxApp args := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv source target (.err error) middle start argsRun noType argsSafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList, renumber]
        rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, argsRel, middleRel⟩ :=
        argsIH env nextEnv source target (.val values) middle start argsRun argsNoType argsSafe envRel stateRel
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val nextValues =>
        have same := doWordApp_related source.maxApp op (List.rel_reverse argsRel)
        cases numeric : doWordApp op values.reverse with
        | none =>
          rw [evaluate, fixClock_evaluate, argsRun] at run
          simp [doApp, applyNumeric, numeric] at run
          exact False.elim (noType run.1.symm)
        | some value =>
          have valueRel := doWordApp_result_related source.maxApp op values.reverse value numeric
          rw [evaluate, fixClock_evaluate, argsRun] at run
          simp [doApp, applyNumeric, numeric] at run
          obtain ⟨rfl, rfl⟩ := run
          refine ⟨.val [value], targetMiddle, ?_, .cons valueRel .nil, middleRel⟩
          simp only [renumberList, renumber]
          rw [evaluate, fixClock_evaluate, targetRun]
          simp [doApp, applyNumeric, ← same, numeric]

/-- Proof-side simulation obligation for a closure primitive dispatcher. -/
def PrimitiveSimulation {C F : Type} (op : ClosLang.Op) : Prop :=
  ∀ (args nextArgs : List Value) (source : State (Nat × C) F) (target : State C F),
    List.Forall₂ (ValueRel source.maxApp) args nextArgs → StateRel source target →
    match doApp op args source with
    | .err error => ∃ targetError,
        doApp op nextArgs target = .err targetError ∧
        ResultRel source.maxApp (.err error) (.err targetError)
    | .val (value, next) => ∃ targetValue targetNext,
        doApp op nextArgs target = .val (targetValue, targetNext) ∧
        ValueRel source.maxApp value targetValue ∧ StateRel next targetNext

/-- An ordinary primitive expression composes argument evaluation with its
    primitive-dispatch simulation. Installation and forcing are separate. -/
theorem evaluate_ordinaryOp {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : EvalSimulation (C := C) (F := F) args)
    (primitiveIH : PrimitiveSimulation (C := C) (F := F) op) :
    EvalSimulation (C := C) (F := F) [.op trace op args] := by
  intro env nextEnv source target result sourceNext start run noType safe envRel stateRel
  have argsSafe : ¬ ClosProps.containsAppSome source.maxApp args := by
    cases op <;> simp_all [ClosProps.containsAppSome, ClosProps.containsAppSomeExp]
  rw [evaluate_ordinaryOp_eq trace op args env source notInstall notForce] at run
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv source target (.err error) sourceNext start argsRun noType argsSafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList, renumber]
        rw [evaluate_ordinaryOp_eq trace op _ nextEnv target notInstall notForce, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, argsRel, middleRel⟩ :=
        argsIH env nextEnv source target (.val values) middle start argsRun argsNoType argsSafe envRel stateRel
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at argsRel
      | val nextValues =>
        have maxEq : middle.maxApp = source.maxApp := by
          have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 args env source
          simpa [argsRun] using h
        have relatedArgs : List.Forall₂ (ValueRel middle.maxApp) values.reverse nextValues.reverse := by
          simpa [ResultRel, maxEq] using List.rel_reverse argsRel
        have prim := primitiveIH values.reverse nextValues.reverse middle targetMiddle relatedArgs middleRel
        cases primRun : doApp op values.reverse middle with
        | err error =>
          rw [primRun] at prim
          obtain ⟨targetError, targetPrimRun, errorRel⟩ := prim
          rw [argsRun] at run
          dsimp only at run
          rw [primRun] at run
          cases run
          refine ⟨.err targetError, targetMiddle, ?_, ?_, middleRel⟩
          · simp only [renumberList, renumber]
            rw [evaluate_ordinaryOp_eq trace op _ nextEnv target notInstall notForce, targetRun]
            dsimp only
            rw [targetPrimRun]
          · simpa [maxEq] using errorRel
        | val pair =>
          obtain ⟨value, last⟩ := pair
          rw [primRun] at prim
          obtain ⟨targetValue, targetLast, targetPrimRun, valueRel, lastRel⟩ := prim
          rw [argsRun] at run
          dsimp only at run
          rw [primRun] at run
          cases run
          refine ⟨.val [targetValue], targetLast, ?_, ?_, lastRel⟩
          · simp only [renumberList, renumber]
            rw [evaluate_ordinaryOp_eq trace op _ nextEnv target notInstall notForce, targetRun]
            dsimp only
            rw [targetPrimRun]
          · exact .cons (by simpa [maxEq] using valueRel) .nil

/-- Integer primitives satisfy the shared ordinary-operation obligation. -/
theorem primitiveSimulation_int {C F : Type} (op : ClosLang.IntOp) :
    PrimitiveSimulation (C := C) (F := F) (.intOp op) := by
  intro args nextArgs source target argsRel stateRel
  have same := doIntApp_related source.maxApp op argsRel
  cases run : doIntApp op args with
  | none =>
    simp [doApp, applyNumeric, run, ← same, ResultRel]
  | some value =>
    have valueRel := doIntApp_result_related source.maxApp op args value run
    simp [doApp, applyNumeric, run, ← same, valueRel, stateRel]

/-- Word primitives satisfy the same obligation, using the proof-side
    floating-point model and its documented assumptions. -/
theorem primitiveSimulation_word {C F : Type} (op : ClosLang.WordOp) :
    PrimitiveSimulation (C := C) (F := F) (.wordOp op) := by
  intro args nextArgs source target argsRel stateRel
  have same := doWordApp_related source.maxApp op argsRel
  cases run : doWordApp op args with
  | none =>
    simp [doApp, applyNumeric, run, ← same, ResultRel]
  | some value =>
    have valueRel := doWordApp_result_related source.maxApp op args value run
    simp [doApp, applyNumeric, run, ← same, valueRel, stateRel]

/-- Constructing blocks preserves the tag and relates all fields, including
    captured closures and other non-scalar values. -/
theorem primitiveSimulation_block_cons {C F : Type} (tag : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.cons tag)) := by
  intro args nextArgs source target argsRel stateRel
  simp only [doApp, applyBlock]
  exact ⟨.block tag nextArgs, target, rfl, .block tag args nextArgs argsRel, stateRel⟩

/-- Block construction composes the shared primitive and argument simulations. -/
theorem evaluate_block_cons {C F : Type} (trace : BackendCommon.Tra) (tag : Nat)
    (args : List ClosLang.Exp) (argsIH : EvalSimulation (C := C) (F := F) args) :
    EvalSimulation (C := C) (F := F) [.op trace (.blockOp (.cons tag)) args] :=
  evaluate_ordinaryOp trace _ args (by simp) (by simp) argsIH (primitiveSimulation_block_cons tag)

/-- Global reads preserve missing slots and relate successful values, for
    both fixed and dynamically selected indices. -/
theorem primitiveSimulation_global_read {C F : Type} (index : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.globOp (.global index)) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil =>
    have readRel := stateRel_getGlobal stateRel index
    cases left : (getGlobal index source.globals).join <;>
      cases right : (getGlobal index target.globals).join <;>
      simp_all [OptionRel, doApp, applyGlobal, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | number number =>
        by_cases negative : number < 0
        · simp [doApp, applyGlobal, negative, ResultRel]
        · have readRel := stateRel_getGlobal stateRel number.toNat
          cases left : (getGlobal number.toNat source.globals).join <;>
            cases right : (getGlobal number.toNat target.globals).join <;>
            simp_all [OptionRel, doApp, applyGlobal, ResultRel]
          simp [show ¬ number < 0 by omega, readRel, stateRel]
      | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure =>
        simp [doApp, applyGlobal, ResultRel]
    | cons head tail =>
      cases head <;> simp [doApp, applyGlobal, ResultRel]

/-- Global allocation appends related empty slots and returns unit. -/
theorem primitiveSimulation_global_alloc {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.globOp .allocGlobal) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyGlobal, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | number number =>
        by_cases negative : number < 0
        · simp [doApp, applyGlobal, negative, ResultRel]
        · have appended := stateRel_allocGlobals number.toNat stateRel
          have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
          simp [doApp, applyGlobal, negative, unitRel, appended]
      | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure =>
        simp [doApp, applyGlobal, ResultRel]
    | cons head tail => cases head <;> simp [doApp, applyGlobal, ResultRel]

/-- Initializing a global slot writes related values in corresponding stores;
    initialized or out-of-range slots fail in both executions. -/
theorem primitiveSimulation_global_set {C F : Type} (index : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.globOp (.setGlobal index)) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyGlobal, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have slots := forall₂_getGlobal stateRel.2.2.2.2.2.2.1 index
      have updated : StateRel { source with globals := source.globals.set index (some value) }
          { target with globals := target.globals.set index (some nextValue) } :=
        stateRel_withGlobals _ _ stateRel (forall₂_set stateRel.2.2.2.2.2.2.1 index _ _ head)
      have unitRel : ValueRel source.maxApp unitValue unitValue := .block _ [] [] .nil
      cases left : getGlobal index source.globals with
      | none => cases right : getGlobal index target.globals <;> simp_all [OptionRel, doApp, applyGlobal, ResultRel]
      | some leftValue =>
        cases right : getGlobal index target.globals with
        | none => simp_all [OptionRel]
        | some rightValue =>
          cases leftValue <;> cases rightValue <;> simp_all [OptionRel, doApp, applyGlobal, ResultRel]
    | cons head tail => simp [doApp, applyGlobal, ResultRel]

/-- All global dispatcher cases satisfy the shared primitive obligation. -/
theorem primitiveSimulation_global {C F : Type} (op : ClosLang.GlobOp) :
    PrimitiveSimulation (C := C) (F := F) (.globOp op) := by
  cases op with
  | global index => exact primitiveSimulation_global_read index
  | setGlobal index => exact primitiveSimulation_global_set index
  | allocGlobal => exact primitiveSimulation_global_alloc
  | globalsPtr | setGlobalsPtr =>
    intro args nextArgs source target argsRel stateRel
    simp [doApp, applyGlobal, ResultRel]

/-- Global expressions preserve evaluation through numbering. -/
theorem evaluate_globalOp {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.GlobOp)
    (args : List ClosLang.Exp) (argsIH : EvalSimulation (C := C) (F := F) args) :
    EvalSimulation (C := C) (F := F) [.op trace (.globOp op) args] :=
  evaluate_ordinaryOp trace _ args (by simp) (by simp) argsIH (primitiveSimulation_global op)

/-- Testing a block's tag and length yields the same Boolean after numbering. -/
theorem primitiveSimulation_block_tagLenEq {C F : Type} (tag length : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.tagLenEq tag length)) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have lengths := fieldsRel.length_eq
        have boolRel := boolValue_related source.maxApp (actual == tag && fields.length == length)
        simp [doApp, applyBlock, ← lengths, boolRel, stateRel]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure =>
        simp [doApp, applyBlock, ResultRel]
    | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- A block tag test observes the same constructor tag on related values. -/
theorem primitiveSimulation_block_tagEq {C F : Type} (tag : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.tagEq tag)) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have boolRel := boolValue_related source.maxApp (actual == tag)
        simp [doApp, applyBlock, boolRel, stateRel]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure =>
        simp [doApp, applyBlock, ResultRel]
    | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- Related blocks have equal lengths and therefore agree on length tests. -/
theorem primitiveSimulation_block_lenEq {C F : Type} (length : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.lenEq length)) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have lengths := fieldsRel.length_eq
        have boolRel := boolValue_related source.maxApp (fields.length == length)
        simp [doApp, applyBlock, ← lengths, boolRel, stateRel]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure =>
        simp [doApp, applyBlock, ResultRel]
    | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- Block length returns the same number for corresponding blocks. -/
theorem primitiveSimulation_block_length {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .lengthBlock) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have lengths := fieldsRel.length_eq
        have valueRel : ValueRel source.maxApp (.number fields.length) (.number fields.length) := .number _
        simp [doApp, applyBlock, ← lengths, valueRel, stateRel]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure =>
        simp [doApp, applyBlock, ResultRel]
    | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- Block field lookup returns related values and fails on both sides for an
    out-of-range index. -/
theorem primitiveSimulation_block_elemAt {C F : Type} (index : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.elemAt index)) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | block actual fields nextFields fieldsRel =>
        have lookupRel : OptionRel (ValueRel source.maxApp) fields[index]? nextFields[index]? := by
          simpa [getGlobal] using forall₂_getGlobal fieldsRel index
        cases left : fields[index]? <;> cases right : nextFields[index]? <;>
          simp_all [OptionRel, doApp, applyBlock, ResultRel]
      | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure =>
        simp [doApp, applyBlock, ResultRel]
    | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- Boolean negation observes the same truth value or type error on related
    arguments. -/
theorem primitiveSimulation_block_boolNot {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .boolNot) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have same := valueRel_asBool head
      cases observation : asBool value with
      | none =>
        have targetObservation : asBool nextValue = none := by rw [← same, observation]
        simp [doApp, applyBlock, observation, targetObservation, ResultRel]
      | some boolean =>
        have targetObservation : asBool nextValue = some boolean := by rw [← same, observation]
        have relatedBool := boolValue_related source.maxApp (!boolean)
        simp [doApp, applyBlock, observation, targetObservation, relatedBool, stateRel]
    | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- Boolean block comparisons agree on both arguments, including invalid
    Boolean values and invalid arities. -/
theorem primitiveSimulation_block_boolTest {C F : Type} (test : Flapjack.AstHOL.Test) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.boolTest test)) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyBlock, ResultRel]
    | cons second tail =>
      cases tail with
      | nil =>
        rename_i left nextLeft right nextRight
        have sameLeft := valueRel_asBool first
        have sameRight := valueRel_asBool second
        cases obsLeft : asBool left with
        | none => simp [doApp, applyBlock, ← sameLeft, obsLeft, ResultRel]
        | some x =>
          cases obsRight : asBool right with
          | none => simp [doApp, applyBlock, ← sameLeft, ← sameRight, obsLeft, obsRight, ResultRel]
          | some y =>
            have boolRel := boolValue_related source.maxApp (x == y)
            simp [doApp, applyBlock, ← sameLeft, ← sameRight, obsLeft, obsRight, boolRel, stateRel]
      | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- Block bounds checks agree on related blocks and numeric indices. -/
theorem primitiveSimulation_block_bounds {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .boundsCheckBlock) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyBlock, ResultRel]
    | cons second tail =>
      cases tail with
      | nil =>
        cases first with
        | block tag fields nextFields fieldsRel =>
          cases second with
          | number index =>
            have lengths := fieldsRel.length_eq
            simp [doApp, applyBlock, ← lengths, boolValue_related, stateRel]
          | word64 _ | block _ _ _ _ | byteVector _ | refPtr _ _ | closure | recclosure =>
            simp [doApp, applyBlock, ResultRel]
        | number _ | word64 _ | byteVector _ | refPtr _ _ | closure | recclosure =>
          cases second <;> simp [doApp, applyBlock, ResultRel]
      | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- Converting a closure list to a block preserves its fields and malformed
    lists fail in both executions. -/
theorem primitiveSimulation_block_fromList {C F : Type} (tag : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.fromList tag)) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons head tail =>
    cases tail with
    | nil =>
      rename_i value nextValue
      have decoded := valueToList_related source.maxApp value nextValue head
      cases left : valueToList value <;> cases right : valueToList nextValue <;>
        simp_all [doApp, applyBlock, ResultRel]
      exact .block _ _ _ decoded
    | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- List append preserves element order across numbering and reports malformed
    input lists on both sides. -/
theorem primitiveSimulation_block_listAppend {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .listAppend) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyBlock, ResultRel]
    | cons second tail =>
      cases tail with
      | nil =>
        rename_i left nextLeft right nextRight
        have firstRel := valueToList_related source.maxApp left nextLeft first
        have secondRel := valueToList_related source.maxApp right nextRight second
        cases leftRun : valueToList left <;> cases nextLeftRun : valueToList nextLeft <;>
          cases rightRun : valueToList right <;> cases nextRightRun : valueToList nextRight <;>
          simp_all [doApp, applyBlock, ResultRel]
        exact listToValue_related _ (List.rel_append firstRel secondRel)
      | cons head tail => simp [doApp, applyBlock, ResultRel]

/-- Structural equality has the same result or type error for related
    closure values, including nested blocks and closures. -/
theorem primitiveSimulation_block_equal {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.blockOp .equal) := by
  intro args nextArgs source target argsRel stateRel
  cases argsRel with
  | nil => simp [doApp, applyBlock, ResultRel]
  | cons first tail =>
    cases tail with
    | nil => simp [doApp, applyBlock, ResultRel]
    | cons second tail =>
      cases tail with
      | nil =>
        rename_i left nextLeft right nextRight
        have same := doEq_related source.maxApp left right nextLeft nextRight first second
        cases result : doEq left right with
        | typeError => simp [doApp, applyBlock, ← same, result, ResultRel]
        | val boolean =>
          have boolRel := boolValue_related source.maxApp boolean
          simp [doApp, applyBlock, ← same, result, boolRel, stateRel]
      | cons head tail => simp [doApp, applyBlock, ResultRel]

end Flapjack.Compiler.Backend.ClosNumber

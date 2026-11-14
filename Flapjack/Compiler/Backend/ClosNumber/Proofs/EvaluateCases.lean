module

public import Flapjack.Compiler.Backend.ClosNumber.Proofs.StateRelation
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.Primitive
public import Flapjack.Compiler.Backend.ClosNumber.Proofs.ClosureApplication
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
public import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateLength
public import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate
public import Flapjack.Compiler.Backend.Semantics.ClosProps.InstallConst

@[expose] public section

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

/-- Evaluator simulation at one source state, for arbitrary related targets
and environments. -/
def EvalSimulationAt {C F : Type} (source : State (Nat × C) F) (expressions : List ClosLang.Exp) : Prop :=
  ∀ (env nextEnv : List Value) (target : State C F) (result : Result (List Value) Value)
    (sourceNext : State (Nat × C) F) (start : Nat),
    evaluate expressions env source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) →
    ¬ ClosProps.containsAppSome source.maxApp expressions →
    List.Forall₂ (ValueRel source.maxApp) env nextEnv → StateRel source target →
    ∃ targetResult targetNext,
      evaluate (renumberList start expressions).2 nextEnv target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext

/-- Evaluator simulations available at clocks strictly below the bound. -/
def EvalSimulationBelow {C F : Type} (clock : Nat) (expressions : List ClosLang.Exp) : Prop :=
  ∀ source : State (Nat × C) F, source.clock < clock → EvalSimulationAt source expressions

/-- Restrict a universal simulation to a given source state. -/
theorem evalSimulation_at {C F : Type} {expressions : List ClosLang.Exp}
    (simulation : EvalSimulation (C := C) (F := F) expressions) (source : State (Nat × C) F) :
    EvalSimulationAt source expressions := by
  intro env nextEnv target result next start run noType safe envRel stateRel
  exact simulation env nextEnv source target result next start run noType safe envRel stateRel

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

/-- Indirect applications starting at clocks strictly below the bound. -/
def AppSimulationClockBelow {C F : Type} (clock : Nat) : Prop :=
  ∀ (function nextFunction : Value) (args nextArgs : List Value)
    (source : State (Nat × C) F) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F),
    source.clock < clock →
    evaluateApp none function args source = (result, sourceNext) →
    result ≠ .err (.abort .typeError) → ValueRel source.maxApp function nextFunction →
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
    destClosure_related_partial source.maxApp partialValue function (first :: rest) nextFunction nextArgs
      ⟨related, argsRel, found⟩
  have maxEq : source.maxApp = target.maxApp := stateRel_maxApp source target stateRel
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
  obtain ⟨nextEnv, nextRemaining, start, nextFound, envRel, remainingRel, bodySafe⟩ :=
    destClosure_related_full source.maxApp body () function (first :: rest) nextFunction nextArgs
      bodyEnv remaining ⟨related, argsRel, found⟩
  have maxEq : source.maxApp = target.maxApp := stateRel_maxApp source target stateRel
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
    (bodyIH : EvalSimulationBelow (C := C) (F := F) source.clock [body])
    (applicationIH : AppSimulationClockBelow (C := C) (F := F) source.clock) :
    ∃ targetResult targetNext, evaluateApp none nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
  obtain ⟨nextEnv, nextRemaining, start, nextFound, envRel, remainingRel, bodySafe⟩ :=
    destClosure_related_full source.maxApp body () function (first :: rest) nextFunction nextArgs
      bodyEnv remaining ⟨related, argsRel, found⟩
  have maxEq : source.maxApp = target.maxApp := stateRel_maxApp source target stateRel
  have clockEq : source.clock = target.clock := stateRel.1
  have lengthEq : (first :: rest).length = nextArgs.length := argsRel.length_eq
  have remainingEq : remaining.length = nextRemaining.length := remainingRel.length_eq
  cases argsRel with
  | cons head tail =>
    rename_i nextFirst nextRest
    let cost := (first :: rest).length - remaining.length
    have costPositive : 0 < cost :=
      Nat.sub_pos_of_lt (destClosure_full_remaining_lt _ _ _ _ _ _ _ found)
    have bodyClockLess : (decClock cost source).clock < source.clock := by
      simp [decClock]
      omega
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
        bodyIH (decClock cost source) bodyClockLess bodyEnv nextEnv (decClock cost target)
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
                have lastClockLess : last.clock < source.clock := by
                  have bound := evaluate_clock_le [body] bodyEnv (decClock cost source)
                  rw [bodyRun] at bound
                  exact Nat.lt_of_le_of_lt bound bodyClockLess
                obtain ⟨targetResult, targetNext, targetAppRun, resultRel, nextRel⟩ :=
                  applicationIH value targetValue remaining nextRemaining last targetLast result sourceNext
                    lastClockLess appRun noType (by simpa [lastMax, decClock] using valueRel)
                    (by simpa [lastMax] using remainingRel) lastRel
                refine ⟨targetResult, targetNext, ?_, ?_, nextRel⟩
                · rw [evaluateApp, targetFound]
                  dsimp only
                  rw [if_neg targetEnough, targetCost, fixClock_evaluate]
                  simp only [renumberList] at targetBodyRun
                  rw [targetBodyRun]
                  exact targetAppRun
                · simpa [lastMax] using resultRel

/-- One indirect application step, assuming both recursive simulations only
at smaller clocks. -/
theorem appSimulation_clock_step {C F : Type} (function nextFunction : Value)
    (args nextArgs : List Value) (source : State (Nat × C) F) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F)
    (run : evaluateApp none function args source = (result, sourceNext))
    (noType : result ≠ .err (.abort .typeError))
    (related : ValueRel source.maxApp function nextFunction)
    (argsRel : List.Forall₂ (ValueRel source.maxApp) args nextArgs) (stateRel : StateRel source target)
    (bodyIH : ∀ body, EvalSimulationBelow (C := C) (F := F) source.clock [body])
    (applicationIH : AppSimulationClockBelow (C := C) (F := F) source.clock) :
    ∃ targetResult targetNext, evaluateApp none nextFunction nextArgs target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
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
            result sourceNext run found insufficient noType related argsRel stateRel (bodyIH body) applicationIH

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
  have maxEq : source.maxApp = target.maxApp := stateRel_maxApp source target stateRel
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
theorem evaluate_tick_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State (Nat × C) F) (bodyIH : EvalSimulationAt (decClock 1 source) [body]) :
    EvalSimulationAt source [.tick trace body] := by
  intro env nextEnv target result sourceNext start run noType safe envRel stateRel
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
      bodyIH env nextEnv (decClock 1 target) result sourceNext start
        bodyRun noType bodySafe envRel clocks
    refine ⟨targetResult, targetNext, ?_, resultRel, nextRel⟩
    simpa [renumberList, renumber, evaluate, targetNonzero] using targetRun

/-- Raising a value preserves the numbering relation, assuming the body
simulation. The evaluator's singleton-result theorem supplies the raised value. -/
theorem evaluate_raise_step {C F : Type} (trace : BackendCommon.Tra) (body : ClosLang.Exp)
    (source : State (Nat × C) F) (bodyIH : EvalSimulationAt source [body]) :
    EvalSimulationAt source [.raise trace body] := by
  intro env nextEnv target result sourceNext start run noType safe envRel stateRel
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
        bodyIH env nextEnv target (.err error) bodyNext start bodyRun bodyNoType bodySafe envRel stateRel
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
        bodyIH env nextEnv target (.val values) bodyNext start bodyRun bodyNoType bodySafe envRel stateRel
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
theorem evaluate_cons_step {C F : Type} (first second : ClosLang.Exp) (rest : List ClosLang.Exp)
    (source : State (Nat × C) F) (firstIH : EvalSimulationAt source [first])
    (restIH : ∀ state : State (Nat × C) F, state.clock ≤ source.clock → EvalSimulationAt state (second :: rest)) :
    EvalSimulationAt source (first :: second :: rest) := by
  intro env nextEnv target result sourceNext start run noType safe envRel stateRel
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
        firstIH env nextEnv target (.err error) sourceNext start firstRun noType firstSafe envRel stateRel
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
            firstIH env nextEnv target (.val [value]) middle start firstRun firstNoType firstSafe envRel stateRel
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel tailRel =>
              cases tailRel
              rename_i targetValue
              have middleClock : middle.clock ≤ source.clock := by
                have h := evaluate_clock_le [first] env source
                simpa [firstRun] using h
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
                    restIH middle middleClock env nextEnv targetMiddle (.err error) sourceNext (renumber start first).1
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
                    restIH middle middleClock env nextEnv targetMiddle (.val values) sourceNext (renumber start first).1
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
theorem evaluate_let_step {C F : Type} (trace : BackendCommon.Tra)
    (bindings : List ClosLang.Exp) (body : ClosLang.Exp) (source : State (Nat × C) F)
    (bindingsIH : EvalSimulationAt source bindings)
    (bodyIH : ∀ state : State (Nat × C) F, state.clock ≤ source.clock → EvalSimulationAt state [body]) :
    EvalSimulationAt source [.let trace bindings body] := by
  intro env nextEnv target result sourceNext start run noType safe envRel stateRel
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
        bindingsIH env nextEnv target (.err error) middle start bindingsRun
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
        bindingsIH env nextEnv target (.val values) middle start bindingsRun
          bindingsNoType safeParts.2 envRel stateRel
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at resultRel
      | val targetValues =>
        have middleClock : middle.clock ≤ source.clock := by
          have h := evaluate_clock_le bindings env source
          simpa [bindingsRun] using h
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
          bodyIH middle middleClock (values ++ env) (targetValues ++ nextEnv) targetMiddle result sourceNext
            (renumberList start bindings).1 bodyRun noType bodySafe' extended middleRel
        refine ⟨targetBodyResult, targetLast, ?_, ?_, lastRel⟩
        · simp only [renumberList] at targetBodyRun
          simp only [renumberList, renumber]
          rw [evaluate, fixClock_evaluate, targetRun]
          exact targetBodyRun
        · simpa [maxEq] using bodyRel

/-- A handler preserves normal and abort results and evaluates related handlers
    with related raised values prepended to their environments. -/
theorem evaluate_handle_step {C F : Type} (trace : BackendCommon.Tra)
    (body handler : ClosLang.Exp) (source : State (Nat × C) F)
    (bodyIH : EvalSimulationAt source [body])
    (handlerIH : ∀ state : State (Nat × C) F, state.clock ≤ source.clock → EvalSimulationAt state [handler]) :
    EvalSimulationAt source [.handle trace body handler] := by
  intro env nextEnv target result sourceNext start run noType safe envRel stateRel
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
      bodyIH env nextEnv target bodyResult middle start bodyRun bodyNoType bodySafe envRel stateRel
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
            have middleClock : middle.clock ≤ source.clock := by
              have h := evaluate_clock_le [body] env source
              simpa [bodyRun] using h
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
              handlerIH middle middleClock (value :: env) (targetValue :: nextEnv) targetMiddle result sourceNext
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
theorem evaluate_if_step {C F : Type} (trace : BackendCommon.Tra) (condition yes no : ClosLang.Exp)
    (source : State (Nat × C) F) (conditionIH : EvalSimulationAt source [condition])
    (yesIH : ∀ state : State (Nat × C) F, state.clock ≤ source.clock → EvalSimulationAt state [yes])
    (noIH : ∀ state : State (Nat × C) F, state.clock ≤ source.clock → EvalSimulationAt state [no]) :
    EvalSimulationAt source [.ifThenElse trace condition yes no] := by
  intro env nextEnv target result sourceNext start run noType safe envRel stateRel
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
        conditionIH env nextEnv target (.err error) middle start conditionRun
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
            conditionIH env nextEnv target (.val [value]) middle start conditionRun
              conditionNoType conditionSafe envRel stateRel
          cases targetResult with
          | err error => cases error <;> simp [ResultRel] at resultRel
          | val targetValues =>
            cases resultRel with
            | cons valueRel tailRel =>
              cases tailRel
              rename_i targetValue
              have boolEq : asBool value = asBool targetValue := valueRel_asBool valueRel
              have middleClock : middle.clock ≤ source.clock := by
                have h := evaluate_clock_le [condition] env source
                simpa [conditionRun] using h
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
                    noIH middle middleClock env nextEnv targetMiddle result sourceNext
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
                    yesIH middle middleClock env nextEnv targetMiddle result sourceNext
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
theorem evaluate_letrec_step {C F : Type} (names : List Flapjack.AstHOL.VarN)
    (location : Option Nat) (selected : Option (List Nat))
    (functions : List (Nat × ClosLang.Exp)) (body : ClosLang.Exp) (source : State (Nat × C) F)
    (bodyIH : EvalSimulationAt source [body]) :
    EvalSimulationAt source [.letrec names location selected functions body] := by
  intro env nextEnv target result sourceNext start run noType safe envRel stateRel
  have safeParts : ¬ ClosProps.containsAppSomeFuns source.maxApp functions ∧
      ¬ ClosProps.containsAppSomeExp source.maxApp body := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  have funSafe : ¬ ClosProps.containsAppSome source.maxApp (functions.map Prod.snd) := by
    simpa [ClosProps.containsAppSomeFuns_eq_map] using safeParts.1
  have bodySafe : ¬ ClosProps.containsAppSome source.maxApp [body] := by
    simpa [ClosProps.containsAppSome] using safeParts.2
  have maxEq : source.maxApp = target.maxApp := stateRel_maxApp source target stateRel
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
        bodyIH _ _ target result sourceNext
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

/-- Indirect application at one source state. Argument and function
simulations are limited to reachable clocks, and application is available at
any clock no larger than the starting clock. -/
theorem evaluate_app_step {C F : Type} (trace : BackendCommon.Tra)
    (function : ClosLang.Exp) (args : List ClosLang.Exp)
    (env nextEnv : List Value) (source : State (Nat × C) F) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F) (start : Nat)
    (run : evaluate [.app trace none function args] env source = (result, sourceNext))
    (noType : result ≠ .err (.abort .typeError))
    (safe : ¬ ClosProps.containsAppSome source.maxApp [.app trace none function args])
    (envRel : List.Forall₂ (ValueRel source.maxApp) env nextEnv) (stateRel : StateRel source target)
    (argsIH : EvalSimulationAt source args)
    (functionIH : ∀ state : State (Nat × C) F, state.clock ≤ source.clock → EvalSimulationAt state [function])
    (applicationIH : AppSimulationClockBelow (C := C) (F := F) (source.clock + 1)) :
    ∃ targetResult targetNext,
      evaluate (renumberList start [.app trace none function args]).2 nextEnv target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
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
      have middleClock : middle.clock ≤ source.clock := by
        have h := evaluate_clock_le (first :: rest) env source
        simpa [argsRun] using h
      cases argsResult with
      | err error =>
        rw [evaluate, fixClock_evaluate, argsRun] at run
        cases run
        obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
          argsIH env nextEnv target (.err error) middle (renumber start function).1 argsRun noType safeParts.2.2 envRel stateRel
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
          argsIH env nextEnv target (.val values) middle (renumber start function).1
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
                functionIH middle middleClock env nextEnv targetMiddle (.err error) last start functionRun
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
                    functionIH middle middleClock env nextEnv targetMiddle (.val [value]) last start functionRun
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
                      have lastClock : last.clock ≤ source.clock := by
                        have h := evaluate_clock_le [function] env middle
                        rw [functionRun] at h
                        simp only at h
                        omega
                      obtain ⟨targetResult, targetNext, targetAppRun, resultRel, nextRel⟩ :=
                        applicationIH value targetValue values targetValues last targetLast result sourceNext
                          (by omega) appRun noType (by simpa [lastMax, middleMax] using valueRel)
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

/-- Direct calls at one source state can only propagate an argument error:
the numbering relation makes their code map empty. -/
theorem evaluate_call_step {C F : Type} (trace : BackendCommon.Tra) (ticks location : Nat)
    (args : List ClosLang.Exp) (env nextEnv : List Value)
    (source : State (Nat × C) F) (target : State C F) (result : Result (List Value) Value)
    (sourceNext : State (Nat × C) F) (start : Nat)
    (run : evaluate [.call trace ticks location args] env source = (result, sourceNext))
    (noType : result ≠ .err (.abort .typeError))
    (safe : ¬ ClosProps.containsAppSome source.maxApp [.call trace ticks location args])
    (envRel : List.Forall₂ (ValueRel source.maxApp) env nextEnv) (stateRel : StateRel source target)
    (argsIH : EvalSimulationAt source args) :
    ∃ targetResult targetNext,
      evaluate (renumberList start [.call trace ticks location args]).2 nextEnv target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
  have argsSafe : ¬ ClosProps.containsAppSome source.maxApp args := by
    simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp] using safe
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.err error) middle start argsRun noType argsSafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList, renumber]
        rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.val values) middle start argsRun argsNoType argsSafe envRel stateRel
      have emptyCode : middle.code = HolFiniteMapExact.empty := middleRel.2.2.2.2.2.2.2.2.1
      rw [evaluate, fixClock_evaluate, argsRun] at run
      simp [findCode, emptyCode, HolFiniteMapExact.empty] at run
      exact False.elim (noType run.1.symm)

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

/-- An ordinary primitive step at one source state. Its argument simulation
is needed only at that state. Installation and forcing are separate. -/
theorem evaluate_ordinaryOp_step {C F : Type} (trace : BackendCommon.Tra)
    (op : ClosLang.Op) (args : List ClosLang.Exp)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (env nextEnv : List Value) (source : State (Nat × C) F) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F) (start : Nat)
    (run : evaluate [.op trace op args] env source = (result, sourceNext))
    (noType : result ≠ .err (.abort .typeError))
    (safe : ¬ ClosProps.containsAppSome source.maxApp [.op trace op args])
    (envRel : List.Forall₂ (ValueRel source.maxApp) env nextEnv) (stateRel : StateRel source target)
    (argsIH : EvalSimulationAt source args) (primitiveIH : PrimitiveSimulation (C := C) (F := F) op) :
    ∃ targetResult targetNext,
      evaluate (renumberList start [.op trace op args]).2 nextEnv target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
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
        argsIH env nextEnv target (.err error) sourceNext start argsRun noType argsSafe envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList, renumber]
        rw [evaluate_ordinaryOp_eq trace op _ nextEnv target notInstall notForce, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, argsRel, middleRel⟩ :=
        argsIH env nextEnv target (.val values) middle start argsRun argsNoType argsSafe envRel stateRel
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

/-- Primitive operations preserve the numbering relation. -/
theorem primitiveSimulation_all {C F : Type} (op : ClosLang.Op) :
    PrimitiveSimulation (C := C) (F := F) op := by
  intro args nextArgs source target argsRel stateRel
  have sim := PrimitivePort.do_app_lemma source target args nextArgs op ⟨stateRel, argsRel⟩
  cases run : doApp op args source with
  | err error =>
    simp only [run] at sim
    obtain ⟨targetError, targetRun, errorRel⟩ := sim
    refine ⟨targetError, targetRun, ?_⟩
    cases error <;> cases targetError <;> exact errorRel
  | val pair =>
    obtain ⟨value, next⟩ := pair
    simp only [run] at sim
    obtain ⟨targetValue, targetNext, valueRel, ⟨_, nextRel⟩, targetRun⟩ := sim
    exact ⟨targetValue, targetNext, targetRun, valueRel, nextRel⟩
/-- Thunk inspection preserves its cases and relates the stored value. -/
def DestThunkRel (maxApp : Nat) : DestThunkResult → DestThunkResult → Prop
  | .badRef, .badRef | .notThunk, .notThunk => True
  | .isThunk mode left, .isThunk nextMode right => mode = nextMode ∧ ValueRel maxApp left right
  | _, _ => False

/-- Inspecting related values in related stores gives related thunk results. -/
theorem destThunk_related {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (value nextValue : Value) (valueRel : ValueRel source.maxApp value nextValue)
    (stateRel : StateRel source target) :
    DestThunkRel source.maxApp (destThunk [value] source.refs) (destThunk [nextValue] target.refs) := by
  cases valueRel with
  | refPtr flag index =>
    have refsRel := stateRel.2.2.2.2.2.1 index
    cases left : source.refs.lookup index <;> cases right : target.refs.lookup index <;>
      simp_all [optionRel, RefRel, destThunk, DestThunkRel]
    rename_i leftRef rightRef
    cases leftRef <;> cases rightRef <;> simp_all
    cases flag <;> simp_all
  | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure =>
    simp [destThunk, DestThunkRel]

/-- Thunk inspection also preserves invalid-arity cases for related lists. -/
theorem destThunk_list_related {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (values nextValues : List Value) (valuesRel : List.Forall₂ (ValueRel source.maxApp) values nextValues)
    (stateRel : StateRel source target) :
    DestThunkRel source.maxApp (destThunk values source.refs) (destThunk nextValues target.refs) := by
  cases valuesRel with
  | nil => simp [destThunk, DestThunkRel]
  | cons head tail =>
    cases tail with
    | nil => exact destThunk_related source target _ _ head stateRel
    | cons next tail => simp [destThunk, DestThunkRel]

/-- The force-result update succeeds or fails together and preserves related
    stores when it writes an evaluated thunk. -/
theorem updateThunk_related {C F : Type} (source : State (Nat × C) F) (target : State C F)
    (values nextValues results nextResults : List Value)
    (valuesRel : List.Forall₂ (ValueRel source.maxApp) values nextValues)
    (resultsRel : List.Forall₂ (ValueRel source.maxApp) results nextResults)
    (stateRel : StateRel source target) :
    match updateThunk values source.refs results with
    | none => updateThunk nextValues target.refs nextResults = none
    | some refs => ∃ nextRefs, updateThunk nextValues target.refs nextResults = some nextRefs ∧
        StateRel { source with refs := refs } { target with refs := nextRefs } := by
  cases valuesRel with
  | nil => simp [updateThunk]
  | cons pointer tail =>
    cases tail with
    | cons head tail => simp [updateThunk]
    | nil =>
      cases resultsRel with
      | nil => simp [updateThunk]
      | cons value tail =>
        cases tail with
        | cons head tail => simp [updateThunk]
        | nil =>
          cases pointer with
          | refPtr flag index =>
            cases flag with
            | true => simp [updateThunk]
            | false =>
              rename_i result nextResult
              have inspected := destThunk_related source target result nextResult value stateRel
              cases left : destThunk [result] source.refs <;>
                cases right : destThunk [nextResult] target.refs <;>
                simp_all [DestThunkRel, updateThunk]
              have refsRel := stateRel.2.2.2.2.2.1 index
              cases leftRef : source.refs.lookup index <;> cases rightRef : target.refs.lookup index <;>
                simp_all [optionRel, RefRel, storeThunk]
              rename_i sourceRef targetRef
              cases sourceRef <;> cases targetRef <;> simp_all
              rename_i leftMode leftValue rightMode rightValue
              cases leftMode <;> cases rightMode <;> simp_all
              have updated := stateRel_updateRefs index (.thunk .evaluated result)
                (.thunk .evaluated nextResult) stateRel ⟨rfl, value⟩
              exact updated
          | number _ | word64 _ | block _ _ _ _ | byteVector _ | closure | recclosure =>
            simp [updateThunk]

/-- Forcing a thunk composes argument evaluation, thunk inspection, evaluation
    of the forced function and the related store update. The generated-call
    simulation is a remaining mutual-evaluator induction hypothesis. -/
theorem evaluate_forceThunk_step {C F : Type} (trace : BackendCommon.Tra) (args : List ClosLang.Exp)
    (env nextEnv : List Value) (source : State (Nat × C) F) (target : State C F)
    (result : Result (List Value) Value) (sourceNext : State (Nat × C) F) (start : Nat)
    (run : evaluate [.op trace (.thunkOp .forceThunk) args] env source = (result, sourceNext))
    (noType : result ≠ .err (.abort .typeError))
    (safe : ¬ ClosProps.containsAppSome source.maxApp [.op trace (.thunkOp .forceThunk) args])
    (envRel : List.Forall₂ (ValueRel source.maxApp) env nextEnv) (stateRel : StateRel source target)
    (argsIH : EvalSimulationAt source args)
    (forceIH : ∀ state : State (Nat × C) F, state.clock ≤ source.clock →
      EvalSimulationAt state [appUnit (.var .none 0)]) :
    ∃ targetResult targetNext,
      evaluate (renumberList start [.op trace (.thunkOp .forceThunk) args]).2 nextEnv target = (targetResult, targetNext) ∧
      ResultRel source.maxApp result targetResult ∧ StateRel sourceNext targetNext := by
  have safeParts : 1 ≤ source.maxApp ∧ ¬ ClosProps.containsAppSome source.maxApp args := by
    have h : source.maxApp ≠ 0 ∧ ¬ ClosProps.containsAppSome source.maxApp args := by
      simpa [ClosProps.containsAppSome, ClosProps.containsAppSomeExp, not_or] using safe
    exact ⟨by omega, h.2⟩
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [evaluate, fixClock_evaluate, argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env nextEnv target (.err error) middle start argsRun noType safeParts.2 envRel stateRel
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        simp only [renumberList, renumber]
        rw [evaluate, fixClock_evaluate, targetRun]
    | val values =>
      have argsNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, valuesRel, middleRel⟩ :=
        argsIH env nextEnv target (.val values) middle start argsRun argsNoType safeParts.2 envRel stateRel
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at valuesRel
      | val nextValues =>
        have middleClock : middle.clock ≤ source.clock := by
          have h := evaluate_clock_le args env source
          simpa [argsRun] using h
        have middleMax : middle.maxApp = source.maxApp := by
          have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1 args env source
          simpa [argsRun] using h
        have relatedValues : List.Forall₂ (ValueRel middle.maxApp) values nextValues := by
          simpa [ResultRel, middleMax] using valuesRel
        have inspected := destThunk_list_related middle targetMiddle values nextValues relatedValues middleRel
        rw [evaluate, fixClock_evaluate, argsRun] at run
        dsimp only at run
        cases sourceThunk : destThunk values middle.refs with
        | badRef =>
          rw [sourceThunk] at run
          simp at run
          exact False.elim (noType run.1.symm)
        | notThunk =>
          rw [sourceThunk] at run
          simp at run
          exact False.elim (noType run.1.symm)
        | isThunk mode value =>
          cases targetThunk : destThunk nextValues targetMiddle.refs with
          | badRef => simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          | notThunk => simp [DestThunkRel, sourceThunk, targetThunk] at inspected
          | isThunk targetMode targetValue =>
            have rel : mode = targetMode ∧ ValueRel middle.maxApp value targetValue := by
              simpa [DestThunkRel, sourceThunk, targetThunk] using inspected
            obtain ⟨rfl, valueRel⟩ := rel
            cases mode with
            | evaluated =>
              rw [sourceThunk] at run
              cases run
              refine ⟨.val [targetValue], targetMiddle, ?_, ?_, middleRel⟩
              · simp only [renumberList, renumber]
                rw [evaluate, fixClock_evaluate, targetRun]
                dsimp only
                rw [targetThunk]
              · exact .cons (by simpa [middleMax] using valueRel) .nil
            | notEvaluated =>
              have forceSafe : ¬ ClosProps.containsAppSome middle.maxApp [appUnit (.var .none 0)] := by
                simp [ClosProps.containsAppSome, ClosProps.containsAppSomeExp, appUnit, middleMax]
                omega
              cases forceRun : evaluate [appUnit (.var .none 0)] [value] middle with
              | mk forceResult last =>
                cases forceResult with
                | err error =>
                  rw [sourceThunk] at run
                  dsimp only at run
                  rw [forceRun] at run
                  cases run
                  obtain ⟨targetForceResult, targetLast, targetForceRun, resultRel, lastRel⟩ :=
                    forceIH middle middleClock [value] [targetValue] targetMiddle (.err error) last 0 forceRun noType
                      forceSafe (.cons valueRel .nil) middleRel
                  cases targetForceResult with
                  | val values => cases error <;> simp [ResultRel] at resultRel
                  | err targetError =>
                    refine ⟨.err targetError, targetLast, ?_, ?_, lastRel⟩
                    · simp [renumberList, renumber, appUnit] at targetForceRun
                      simp only [renumberList, renumber]
                      rw [evaluate, fixClock_evaluate, targetRun]
                      dsimp only
                      rw [targetThunk]
                      dsimp only
                      simp only [appUnit]
                      rw [targetForceRun]
                    · simpa [middleMax] using resultRel
                | val forced =>
                  have forceNoType : (Result.val forced : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
                  obtain ⟨targetForceResult, targetLast, targetForceRun, resultRel, lastRel⟩ :=
                    forceIH middle middleClock [value] [targetValue] targetMiddle (.val forced) last 0 forceRun forceNoType
                      forceSafe (.cons valueRel .nil) middleRel
                  cases targetForceResult with
                  | err error => cases error <;> simp [ResultRel] at resultRel
                  | val nextForced =>
                    have lastMax : last.maxApp = middle.maxApp := by
                      have h := (ClosProps.evaluate_const (C := Nat × C) (F := F)).1
                        [appUnit (.var .none 0)] [value] middle
                      simpa [forceRun] using h
                    have forcedRel : List.Forall₂ (ValueRel last.maxApp) forced nextForced := by
                      simpa [ResultRel, lastMax] using resultRel
                    have pointerRel : List.Forall₂ (ValueRel last.maxApp) values nextValues := by
                      simpa [lastMax] using relatedValues
                    have update := updateThunk_related last targetLast values nextValues forced nextForced
                      pointerRel forcedRel lastRel
                    cases updateRun : updateThunk values last.refs forced with
                    | none =>
                      rw [sourceThunk] at run
                      dsimp only at run
                      rw [forceRun] at run
                      dsimp only at run
                      rw [updateRun] at run
                      simp at run
                      exact False.elim (noType run.1.symm)
                    | some refs =>
                      rw [updateRun] at update
                      obtain ⟨targetRefs, targetUpdate, updatedRel⟩ := update
                      rw [sourceThunk] at run
                      dsimp only at run
                      rw [forceRun] at run
                      dsimp only at run
                      rw [updateRun] at run
                      cases run
                      refine ⟨.val nextForced, { targetLast with refs := targetRefs }, ?_, ?_, updatedRel⟩
                      · simp [renumberList, renumber, appUnit] at targetForceRun
                        simp only [renumberList, renumber]
                        rw [evaluate, fixClock_evaluate, targetRun]
                        dsimp only
                        rw [targetThunk]
                        dsimp only
                        simp only [appUnit]
                        rw [targetForceRun]
                        dsimp only
                        rw [targetUpdate]
                      · simpa [ResultRel, lastMax, middleMax] using forcedRel

end Flapjack.Compiler.Backend.ClosNumber

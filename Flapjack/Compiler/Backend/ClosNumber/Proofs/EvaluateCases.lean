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

end Flapjack.Compiler.Backend.ClosNumber

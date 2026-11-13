module

public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.StateRel
public import Flapjack.Compiler.Backend.BvlToBvi.Proofs.StateOk
public import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
public import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList
public import Flapjack.Compiler.Backend.Semantics.BviProps.Clock

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.BvlToBvi.SourceSing
@[expose] public section

/-! Cases of the BVL-to-BVI evaluator simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- The source simulation's result mapping, specialized to relocated BVL
values and BVI exception results. This is Flapjack infrastructure. -/
def mapSimulationResult (relocate : Nat → Nat) : Result (List Value) Value → BviSem.BviResult
  | .val values => .val (values.map (adjustBv relocate))
  | .err (.abort reason) => .err (.abort reason)
  | .err (.raise value) => .err (.raise (.exn (adjustBv relocate value)))

/-- The source-shaped simulation proposition used for induction hypotheses.
This is Flapjack infrastructure until the source evaluator qualification and
complete pass-correctness proof are available. -/
def simulation {C F : Type} (xs : List Bvl.Exp) (env : List Value)
    (source : BvlSem.State (Nat × C) F) : Prop :=
  ∀ (n : Nat) (res : Result (List Value) Value) (next : BvlSem.State (Nat × C) F)
    (target : BviSem.BviState C F) (n2 : Nat) (ys : List Bvi.Exp)
    (aux : AppList (Nat × Nat × Bvi.Exp)) (relocate : Nat → Nat),
    BvlSem.evaluate xs env source = (res, next) →
    res ≠ .err (.abort .typeError) →
    compileListSource n xs = (ys, aux, n2) →
    stateRel relocate source target → stateOk source → bvOkList source.refs env →
    auxCodeInstalled (appListAppend aux) target.code →
    BvlHandle.Proofs.handleOk xs → target.global.isSome = true →
    ∃ targetNext newRelocate clock,
      BviSem.evaluate ys (env.map (adjustBv newRelocate)) (BviProps.incClock clock target) =
        (mapSimulationResult newRelocate res, targetNext) ∧
      stateRel newRelocate next targetNext ∧
      env.map (adjustBv relocate) = env.map (adjustBv newRelocate) ∧
      ∀ key, source.refs.lookup key ≠ none → relocate key = newRelocate key

/-- The empty-list case of the source evaluator simulation, untagged until
the BVI evaluator and full induction theorem are source-reviewed. -/
theorem simulation_nil {C F : Type} (env : List Value) (source : BvlSem.State (Nat × C) F) :
    simulation [] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  simp [BvlSem.evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  simp [compileListSource] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
  · simp [BviSem.evaluate, BviProps.incClock, mapSimulationResult]
  · intro key member
    rfl

/-- The variable case of the source evaluator simulation. The original
no-type-error premise excludes out-of-range variables. Untagged pending BVI
evaluator and full induction review. -/
theorem simulation_var {C F : Type} (index : Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F) : simulation [.var index] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  cases lookup : env[index]? with
  | none =>
    simp [BvlSem.evaluate, lookup] at run
    rcases run with ⟨rfl, _⟩
    exact (notTypeError rfl).elim
  | some value =>
    simp [BvlSem.evaluate, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    simp [compileListSource, compileSingSource, smartAppend] at compiled
    rcases compiled with ⟨rfl, rfl, rfl⟩
    refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
    · simp [BviSem.evaluate, BviProps.incClock, mapSimulationResult, lookup]
    · intro key member
      rfl

/-- The tick case follows from the body at one less clock. Untagged pending
BVI evaluator qualification and full induction review. -/
theorem simulation_tick {C F : Type} (body : Bvl.Exp) (env : List Value)
    (source : BvlSem.State (Nat × C) F) (ih : simulation [body] env (BvlSem.decClock 1 source)) :
    simulation [.tick body] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases hbody : compileSingSource n body with ⟨converted, code, finalName⟩
  have nilRight : smartAppend code .nil = code := by cases code <;> rfl
  have bodyCompiled : compileListSource n [body] = ([converted], code, finalName) := by
    simp [compileListSource, hbody, nilRight]
  simp [compileListSource, compileSingSource, hbody, nilRight] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have clocks : source.clock = target.clock := related.2.2.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by omega
    have targetReset : { target with clock := 0 } = target := by
      cases target
      simp_all
    simp [BvlSem.evaluate, zero] at run
    rcases run with ⟨rfl, rfl⟩
    refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
    · simp [BviSem.evaluate, BviProps.incClock, targetZero, targetReset, mapSimulationResult]
    · intro key member
      rfl
  · have targetNonzero : target.clock ≠ 0 := by omega
    have bodyRun : BvlSem.evaluate [body] env (BvlSem.decClock 1 source) = (res, next) := by
      simpa [BvlSem.evaluate, zero] using run
    have relatedDec := stateRel_decClock relocate source target related 1
    have sourceOkDec : stateOk (BvlSem.decClock 1 source) := (evaluateOk_lemma 1 source).1.2 sourceOk
    have bodyHandlers : BvlHandle.Proofs.handleOk [body] := by
      simpa [BvlHandle.Proofs.handleOk] using handlers
    obtain ⟨targetNext, newRelocate, clock, targetRun, relatedNext, envEq, refsEq⟩ :=
      ih n res next (BviSem.decClock 1 target) finalName [converted] code relocate bodyRun notTypeError
        bodyCompiled relatedDec sourceOkDec envOk installed bodyHandlers global
    refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
    have targetClock : (BviProps.incClock clock target).clock ≠ 0 := by
      simp only [BviProps.incClock]
      omega
    rw [BviSem.evaluate]
    simp only [if_neg targetClock]
    rw [BviProps.decClock_incClock_one target clock targetNonzero]
    exact targetRun

/-- The raise case follows from the body simulation. Untagged pending BVI
evaluator qualification and full induction review. -/
theorem simulation_raise {C F : Type} (body : Bvl.Exp) (env : List Value)
    (source : BvlSem.State (Nat × C) F) (ih : simulation [body] env source) :
    simulation [.raise body] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases hbody : compileSingSource n body with ⟨converted, code, finalName⟩
  have nilRight : smartAppend code .nil = code := by cases code <;> rfl
  have bodyCompiled : compileListSource n [body] = ([converted], code, finalName) := by
    simp [compileListSource, hbody, nilRight]
  simp [compileListSource, compileSingSource, hbody, nilRight] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have bodyHandlers : BvlHandle.Proofs.handleOk [body] := by
    simpa [BvlHandle.Proofs.handleOk] using handlers
  cases bodyRun : BvlSem.evaluate [body] env source with
  | mk bodyResult bodyNext =>
    cases bodyResult with
    | val values =>
      obtain ⟨value, rfl⟩ := BvlSem.evaluate_singleton body env source bodyNext values bodyRun
      simp [BvlSem.evaluate, bodyRun] at run
      rcases run with ⟨rfl, rfl⟩
      have bodyNotType : (Result.val [value] : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetNext, newRelocate, clock, targetRun, relatedNext, envEq, refsEq⟩ :=
        ih n (.val [value]) bodyNext target finalName [converted] code relocate bodyRun bodyNotType
          bodyCompiled related sourceOk envOk installed bodyHandlers global
      refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
      rw [BviSem.evaluate]
      simp [mapSimulationResult] at targetRun
      rw [targetRun]
      rfl
    | err error =>
      simp [BvlSem.evaluate, bodyRun] at run
      rcases run with ⟨rfl, rfl⟩
      obtain ⟨targetNext, newRelocate, clock, targetRun, relatedNext, envEq, refsEq⟩ :=
        ih n (.err error) bodyNext target finalName [converted] code relocate bodyRun notTypeError
          bodyCompiled related sourceOk envOk installed bodyHandlers global
      refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
      rw [BviSem.evaluate, targetRun]
      cases error <;> rfl

/-- Relocation leaves Boolean decoding unchanged. This Flapjack helper is
used to compare conditional branches in the simulation. -/
theorem asBool_adjustBv (relocate : Nat → Nat) (value : Value) :
    BvlSem.asBool (adjustBv relocate value) = BvlSem.asBool value := by
  cases value with
  | block tag values => cases values <;> simp [adjustBv, adjustValues, BvlSem.asBool]
  | _ => simp [adjustBv, BvlSem.asBool]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

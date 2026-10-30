import Flapjack.Compiler.Backend.BvlToBvi.Proofs.StateRel
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.StateOk
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList
import Flapjack.Compiler.Backend.Semantics.BviProps.Clock

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

/-- Empty-list case of the source evaluator simulation. It retains the
source theorem's hypotheses and existential result, but is untagged until the
underlying BVI evaluator and the full induction theorem are source-reviewed. -/
theorem compileExpsCorrect_nil {C F : Type} (env : List Value)
    (source next : BvlSem.State (Nat × C) F) (n n2 : Nat)
    (res : Result (List Value) Value) (target : BviSem.BviState C F)
    (ys : List Bvi.Exp) (aux : AppList (Nat × Nat × Bvi.Exp)) (relocate : Nat → Nat)
    (run : BvlSem.evaluate [] env source = (res, next))
    (_notTypeError : res ≠ .err (.abort .typeError))
    (compiled : compileListSource n [] = (ys, aux, n2))
    (related : stateRel relocate source target)
    (_sourceOk : stateOk source) (_envOk : bvOkList source.refs env)
    (_installed : auxCodeInstalled (appListAppend aux) target.code)
    (_handlers : BvlHandle.Proofs.handleOk []) (_global : target.global.isSome = true) :
    ∃ targetNext newRelocate clock,
      BviSem.evaluate ys (env.map (adjustBv newRelocate)) (BviProps.incClock clock target) =
        (mapSimulationResult newRelocate res, targetNext) ∧
      stateRel newRelocate next targetNext ∧
      env.map (adjustBv relocate) = env.map (adjustBv newRelocate) ∧
      ∀ key, source.refs.lookup key ≠ none → relocate key = newRelocate key := by
  simp [BvlSem.evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  simp [compileListSource] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
  · simp [BviSem.evaluate, BviProps.incClock, mapSimulationResult]
  · intro key member
    rfl

/-- Variable case of the source evaluator simulation. An out-of-range
variable is excluded by the original no-type-error premise. This remains
untagged while BVI evaluation and the full induction theorem are reviewed. -/
theorem compileExpsCorrect_var {C F : Type} (index : Nat) (env : List Value)
    (source next : BvlSem.State (Nat × C) F) (n n2 : Nat)
    (res : Result (List Value) Value) (target : BviSem.BviState C F)
    (ys : List Bvi.Exp) (aux : AppList (Nat × Nat × Bvi.Exp)) (relocate : Nat → Nat)
    (run : BvlSem.evaluate [.var index] env source = (res, next))
    (notTypeError : res ≠ .err (.abort .typeError))
    (compiled : compileListSource n [.var index] = (ys, aux, n2))
    (related : stateRel relocate source target)
    (_sourceOk : stateOk source) (_envOk : bvOkList source.refs env)
    (_installed : auxCodeInstalled (appListAppend aux) target.code)
    (_handlers : BvlHandle.Proofs.handleOk [.var index]) (_global : target.global.isSome = true) :
    ∃ targetNext newRelocate clock,
      BviSem.evaluate ys (env.map (adjustBv newRelocate)) (BviProps.incClock clock target) =
        (mapSimulationResult newRelocate res, targetNext) ∧
      stateRel newRelocate next targetNext ∧
      env.map (adjustBv relocate) = env.map (adjustBv newRelocate) ∧
      ∀ key, source.refs.lookup key ≠ none → relocate key = newRelocate key := by
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

/-- Tick case of the source simulation, using its induction hypothesis for
the body at the decremented source state. This remains untagged pending BVI
evaluator qualification and the full induction theorem. -/
theorem compileExpsCorrect_tick {C F : Type} (body : Bvl.Exp) (env : List Value)
    (source next : BvlSem.State (Nat × C) F) (n n2 : Nat)
    (res : Result (List Value) Value) (target : BviSem.BviState C F)
    (ys : List Bvi.Exp) (aux : AppList (Nat × Nat × Bvi.Exp)) (relocate : Nat → Nat)
    (ih : simulation [body] env (BvlSem.decClock 1 source))
    (run : BvlSem.evaluate [.tick body] env source = (res, next))
    (notTypeError : res ≠ .err (.abort .typeError))
    (compiled : compileListSource n [.tick body] = (ys, aux, n2))
    (related : stateRel relocate source target)
    (sourceOk : stateOk source) (envOk : bvOkList source.refs env)
    (installed : auxCodeInstalled (appListAppend aux) target.code)
    (handlers : BvlHandle.Proofs.handleOk [.tick body]) (global : target.global.isSome = true) :
    ∃ targetNext newRelocate clock,
      BviSem.evaluate ys (env.map (adjustBv newRelocate)) (BviProps.incClock clock target) =
        (mapSimulationResult newRelocate res, targetNext) ∧
      stateRel newRelocate next targetNext ∧
      env.map (adjustBv relocate) = env.map (adjustBv newRelocate) ∧
      ∀ key, source.refs.lookup key ≠ none → relocate key = newRelocate key := by
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
    have sourceOkDec : stateOk (BvlSem.decClock 1 source) := (stateOk_decClock 1 source).2 sourceOk
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

/-- The empty-list induction proposition holds. -/
theorem simulation_nil {C F : Type} (env : List Value) (source : BvlSem.State (Nat × C) F) :
    simulation [] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  exact compileExpsCorrect_nil env source next n n2 res target ys aux relocate run notTypeError
    compiled related sourceOk envOk installed handlers global

/-- The variable induction proposition holds. -/
theorem simulation_var {C F : Type} (index : Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F) : simulation [.var index] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  exact compileExpsCorrect_var index env source next n n2 res target ys aux relocate run notTypeError
    compiled related sourceOk envOk installed handlers global

/-- The tick induction proposition follows from the body at one less clock. -/
theorem simulation_tick {C F : Type} (body : Bvl.Exp) (env : List Value)
    (source : BvlSem.State (Nat × C) F) (ih : simulation [body] env (BvlSem.decClock 1 source)) :
    simulation [.tick body] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  exact compileExpsCorrect_tick body env source next n n2 res target ys aux relocate ih run notTypeError
    compiled related sourceOk envOk installed handlers global

/-- Any finite sequence of ticks around a variable satisfies the simulation.
This is a Flapjack consequence of the checked cases, not a separate HOL port. -/
theorem simulation_ticks_var {C F : Type} (count index : Nat) (env : List Value)
    (source : BvlSem.State (Nat × C) F) : simulation [Bvl.mkTick count (.var index)] env source := by
  induction count generalizing source with
  | zero => exact simulation_var index env source
  | succ count ih => exact simulation_tick _ env source (ih (BvlSem.decClock 1 source))

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

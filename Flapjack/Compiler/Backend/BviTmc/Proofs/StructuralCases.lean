import Flapjack.Compiler.Backend.BviTmc.Proofs.StructuralHypothesis
import Flapjack.Compiler.Backend.BviTmc.Proofs.ReturnSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.RaiseSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.TickSimulation
import Flapjack.Compiler.Backend.BviTmc.Proofs.IfAssembly
import Flapjack.Compiler.Backend.BviTmc.Proofs.LetAssembly

/-! Singleton expression cases for the TMC structural induction. -/
namespace Flapjack.Compiler.Backend.BviTmc.StructuralCases
open BviTmc BviSem BvlSem ListSimulation ClockHypothesis StructuralHypothesis

/-- Flapjack infrastructure: the singleton simulation in the shape used by
the earlier case proofs, with explicit worker indices and result names. -/
def RawSingletonPost {C F : Type} (e : Bvi.Exp) (source : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (loc : Nat) (result : BviResult) (final : BviState (Nat × C) F) : Prop :=
  ∃ (next : BviState C F) (nextMap : HolFiniteMapExact Nat Nat) (nextResult : BviResult),
    evaluate [e] env2 target = (nextResult, next) ∧
    SemanticPrimitivesProps.resultRel (List.Forall₂ (valueRel nextMap)) (ResultRelation.eorRel nextMap) result nextResult ∧
    stateRel nextMap final next ∧ finiteSubmap f nextMap ∧ onlyFresh f nextMap target.refs ∧
    holesUnchangedExcept f target.refs next.refs ∅ ∧ holesStillNotFinalised f target.refs next.refs ∧
    ∀ dest, optimisedCode loc dest source.code target.code →
      (∀ wrapper, ([e] : List Bvi.Exp).length = 1 ∧ rewriteWrapperSource loc dest env1.length e = some wrapper →
        Core [wrapper] env2 f target result final) ∧
      (opt = true → ∀ i j ptr work,
        i = env1.length ∧ j = env1.length + 1 ∧ (∃ c, holeHasVal f env1 env2 target.refs c) ∧
        holeNotFinalised target.refs ptr ∧ rewriteWorkerSource loc dest i j env1.length e = work ∧
        holEl i env2 = .refPtr false ptr → IfWorker.WorkerCore work env1 env2 f target ptr result final)

/-- Flapjack infrastructure: convert the earlier explicit singleton
conclusion to the factored form used by the structural induction. -/
theorem raw_to_singleton {C F : Type} (e : Bvi.Exp) (source : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (loc : Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (raw : RawSingletonPost e source target env1 env2 opt f loc result final) :
    SingletonPost e source target env1 env2 opt f loc result final := by
  obtain ⟨next, g, targetResult, run, related, states, extension, fresh, unchanged, still, optimized⟩ := raw
  refine ⟨⟨next, g, targetResult, run, related, states, extension, fresh, unchanged, still⟩, ?_⟩
  intro dest code
  obtain ⟨wrapper, worker⟩ := optimized dest code
  exact ⟨fun w rewrite => wrapper w ⟨rfl, rewrite⟩,
    fun optTrue ptr c hole notFinal pointer => worker optTrue env1.length (env1.length + 1) ptr
      (rewriteWorkerSource loc dest env1.length (env1.length + 1) env1.length e)
      ⟨rfl, rfl, ⟨c, hole⟩, notFinal, rfl, pointer⟩⟩

/-- Flapjack infrastructure: expand the factored singleton conclusion for
case proofs that still use explicit worker indices. -/
theorem singleton_to_raw {C F : Type} (e : Bvi.Exp) (source : BviState (Nat × C) F)
    (target : BviState C F) (env1 env2 : List Value) (opt : Bool) (f : HolFiniteMapExact Nat Nat)
    (loc : Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (post : SingletonPost e source target env1 env2 opt f loc result final) :
    RawSingletonPost e source target env1 env2 opt f loc result final := by
  obtain ⟨⟨next, g, targetResult, run, related, states, extension, fresh, unchanged, still⟩, optimized⟩ := post
  refine ⟨next, g, targetResult, run, related, states, extension, fresh, unchanged, still, ?_⟩
  intro dest code
  obtain ⟨wrapper, worker⟩ := optimized dest code
  constructor
  · intro w ⟨_, rewrite⟩
    exact wrapper w rewrite
  · intro optTrue i j ptr work ⟨iEq, jEq, ⟨c, hole⟩, notFinal, rewrite, pointer⟩
    subst i
    subst j
    subst work
    exact worker optTrue ptr c hole notFinal pointer

/-- Flapjack infrastructure: the return case follows from the smaller-weight
argument-list hypothesis. -/
theorem evaluate_return_from_weight {C F : Type} (loc : Nat) (args : List Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.return args] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.return args))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.return args])) :
    SingletonPost (.return args) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have argsSafe : ∀ e ∈ args, noMutcons e := fun e member => safe ⟨e, member⟩
  have weight : expsWeight args < expsWeight [.return args] := by
    simp [BviSem.expsWeight, BviSem.expWeight]
    omega
  apply raw_to_singleton
  apply ReturnSimulation.evaluate_return args source env1 result final opt f target env2 loc run notTypeError
  intro childResult childFinal childRun childSafe
  exact (ih args source target env1 env2 false f loc childResult childFinal (Nat.le_refl _) weight childRun argsSafe
    (envRel_relax opt f env1 env2 environments) states (by simp) childSafe).1

/-- Flapjack infrastructure: the raise case follows from the smaller-weight
body hypothesis. -/
theorem evaluate_raise_from_weight {C F : Type} (loc : Nat) (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.raise body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.raise body))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.raise body])) :
    SingletonPost (.raise body) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have weight : expsWeight [body] < expsWeight [.raise body] := by
    simp [BviSem.expsWeight, BviSem.expWeight]
  apply raw_to_singleton
  apply RaiseSimulation.evaluate_raise body source env1 result final opt f target env2 loc run notTypeError
  intro childResult childFinal childRun childSafe
  exact (ih [body] source target env1 env2 false f loc childResult childFinal (Nat.le_refl _) weight childRun
    (by simpa using safe) (envRel_relax opt f env1 env2 environments) states (by simp) childSafe).1

/-- Flapjack infrastructure: the tick case follows from the smaller-clock
singleton hypothesis. -/
theorem evaluate_tick_from_clock {C F : Type} (loc : Nat) (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.tick body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.tick body))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerClockIH (C := C) (F := F) source.clock) :
    SingletonPost (.tick body) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  apply raw_to_singleton
  apply TickSimulation.evaluate_tick body source env1 result final opt f target env2 loc run states
  intro positive bodyRun
  have smaller : (BviSem.decClock 1 source).clock < source.clock := by
    simp [BviSem.decClock]
    omega
  have decStates : stateRel f (BviSem.decClock 1 source) (BviSem.decClock 1 target) := by
    simpa [BviSem.decClock, states.2.1] using stateRel_with_clock (source.clock - 1) f source target states
  have post := ih body (BviSem.decClock 1 source) (BviSem.decClock 1 target) env1 env2 opt f loc result final
    smaller bodyRun safe environments decStates notTypeError
  exact singleton_to_raw body (BviSem.decClock 1 source) (BviSem.decClock 1 target) env1 env2 opt f loc result final post

/-- Flapjack infrastructure: the conditional case follows from the common
smaller-weight induction, including the selected branch's clock bound. -/
theorem evaluate_if_from_weight {C F : Type} (loc : Nat) (condition yes no : Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.ifThenElse condition yes no] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.ifThenElse condition yes no))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.ifThenElse condition yes no])) :
    SingletonPost (.ifThenElse condition yes no) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have conditionWeight : expsWeight [condition] < expsWeight [.ifThenElse condition yes no] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  have yesWeight : expsWeight [yes] < expsWeight [.ifThenElse condition yes no] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  have noWeight : expsWeight [no] < expsWeight [.ifThenElse condition yes no] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  apply IfAssembly.evaluate_if condition yes no source env1 result final opt f target env2 loc
    run notTypeError environments
  · intro r mid conditionRun noError
    exact (ih [condition] source target env1 env2 false f loc r mid (Nat.le_refl _) conditionWeight conditionRun
      (by simpa using safe.1) (envRel_relax opt f env1 env2 environments) states (by simp) noError).1
  · intro branch mid g t ⟨conditionResult, conditionRun⟩ selected branchRun env nextStates
    have clock := evaluate_clock_le [condition] env1 source
    rw [conditionRun] at clock
    have weight : expsWeight [branch] < expsWeight [.ifThenElse condition yes no] := by
      rcases selected with rfl | rfl
      · exact yesWeight
      · exact noWeight
    have branchSafe : noMutcons branch := by
      rcases selected with rfl | rfl
      · exact safe.2.1
      · exact safe.2.2
    exact (ih [branch] mid t env1 env2 opt g loc result final clock weight branchRun
      (by simpa using branchSafe) env nextStates (by simp) notTypeError).2 branch rfl

/-- Flapjack infrastructure: the let case follows from the common
smaller-weight induction for the bindings and body. -/
theorem evaluate_let_from_weight {C F : Type} (loc : Nat) (bindings : List Bvi.Exp) (body : Bvi.Exp)
    (source : BviState (Nat × C) F) (target : BviState C F) (env1 env2 : List Value)
    (opt : Bool) (f : HolFiniteMapExact Nat Nat) (result : BviResult) (final : BviState (Nat × C) F)
    (run : evaluate [.let bindings body] env1 source = (result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) (safe : noMutcons (.let bindings body))
    (environments : envRel opt f env1 env2) (states : stateRel f source target)
    (ih : SmallerWeightIH (C := C) (F := F) source.clock (expsWeight [.let bindings body])) :
    SingletonPost (.let bindings body) source target env1 env2 opt f loc result final := by
  rw [noMutcons.eq_def] at safe
  dsimp only at safe
  have bindingsWeight : expsWeight bindings < expsWeight [.let bindings body] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  have bodyWeight : expsWeight [body] < expsWeight [.let bindings body] := by
    simp only [BviSem.expsWeight, BviSem.expWeight]
    omega
  have bindingsSafe : ∀ e ∈ bindings, noMutcons e := fun e member => safe.1 ⟨e, member⟩
  apply LetAssembly.evaluate_let bindings body source env1 result final opt f target env2 loc
    run notTypeError environments
  · intro r mid bindingsRun noError
    exact (ih bindings source target env1 env2 false f loc r mid (Nat.le_refl _) bindingsWeight bindingsRun
      bindingsSafe (envRel_relax opt f env1 env2 environments) states (by simp) noError).1
  · intro values values' mid g t bindingsRun bodyRun env nextStates
    have clock := evaluate_clock_le bindings env1 source
    rw [bindingsRun] at clock
    exact (ih [body] mid t (values ++ env1) (values' ++ env2) opt g loc result final clock bodyWeight bodyRun
      (by simpa using safe.2) env nextStates (by simp) notTypeError).2 body rfl

end Flapjack.Compiler.Backend.BviTmc.StructuralCases

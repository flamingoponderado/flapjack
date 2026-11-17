module

public import Flapjack.Compiler.Backend.Semantics.DataProps.EvaluatorAssign

@[expose] public section

/-! Compositional evaluator simulation across related stacks. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Same-program simulation on related states with identical locals. For a
continuing execution the resulting locals remain equal; non-type-error stopped executions
retain the empty-live state relation. This is auxiliary infrastructure, not
the HOL evaluator stack-swap theorem. -/
def evaluatorSimulation {C F : Type} (program : DataLang.Prog) : Prop :=
  ∀ (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value)),
    stateRel source target .ln → source.locals = target.locals → exceptionRel source target →
    result ≠ some (.err (.abort .typeError)) →
    DataSem.evaluate program source = (result, sourceNext) →
    ∃ targetNext, DataSem.evaluate program target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals)

/-- Skip preserves same-program simulation. -/
theorem evaluatorSimulation_skip {C F : Type} : evaluatorSimulation (C := C) (F := F) .skip := by
  intro source target sourceNext result related sameLocals exception notType run
  simp [DataSem.evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨target, by simp [DataSem.evaluate], related, fun _ => sameLocals⟩

/-- Moves preserve same-program simulation, including missing-local errors. -/
theorem evaluatorSimulation_move {C F : Type} (dest src : Nat) :
    evaluatorSimulation (C := C) (F := F) (.move dest src) := by
  intro source target sourceNext result related sameLocals exception notType run
  have readEq : DataSem.getVar src source.locals = DataSem.getVar src target.locals := by rw [sameLocals]
  cases read : DataSem.getVar src source.locals with
  | none =>
    have targetRead : DataSem.getVar src target.locals = none := by rw [← readEq, read]
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp [DataSem.evaluate, targetRead], related, by simp⟩
  | some value =>
    have targetRead : DataSem.getVar src target.locals = some value := by rw [← readEq, read]
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    have before := stateRel_of_sameLocals source target (sptDelete dest .ln) related sameLocals
    refine ⟨setVar dest value target, ?_, stateRel_setVar source target .ln dest value before, ?_⟩
    · simp [DataSem.evaluate, targetRead]
    · intro _
      simp [setVar, sameLocals]

/-- Tick preserves same-program simulation in both timeout and continuing
cases. -/
theorem evaluatorSimulation_tick {C F : Type} : evaluatorSimulation (C := C) (F := F) .tick := by
  intro source target sourceNext result related sameLocals exception notType run
  have clockEq := related.2.1
  by_cases zero : source.clock = 0
  · have targetZero : target.clock = 0 := by rw [← clockEq, zero]
    simp [DataSem.evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨flushState true target, by simp [DataSem.evaluate, targetZero], ?_, by simp⟩
    simpa [installSfs] using stateRel_flushInstall source target .ln (.intOp (.const 0)) related
  · have targetNonzero : target.clock ≠ 0 := by rw [← clockEq]; exact zero
    simp [DataSem.evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    have nextRel : stateRel (decClock source) (decClock target) .ln := by
      simpa [stateRel, decClock, clockEq] using related
    exact ⟨decClock target, by simp [DataSem.evaluate, targetNonzero], nextRel, by intro _; exact sameLocals⟩

/-- Space reservation preserves same-program simulation when the two states
begin with identical locals. -/
theorem evaluatorSimulation_makeSpace {C F : Type} (amount : Nat) (names : NumSet) :
    evaluatorSimulation (C := C) (F := F) (.makeSpace amount names) := by
  intro source target sourceNext result related sameLocals exception notType run
  cases cut : cutEnv names source.locals with
  | none =>
    have targetCut : cutEnv names target.locals = none := by rw [← sameLocals, cut]
    simp [DataSem.evaluate, cut] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp [DataSem.evaluate, targetCut], related, by simp⟩
  | some env =>
    have targetCut : cutEnv names target.locals = some env := by rw [← sameLocals, cut]
    simp [DataSem.evaluate, cut] at run
    obtain ⟨rfl, rfl⟩ := run
    have nextRel : stateRel (addSpace { source with locals := env } amount)
        (addSpace { target with locals := env } amount) .ln := by
      rcases related with ⟨code, clock, _, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
      exact ⟨code, clock, rfl, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, by simp [sptMem, sptDomain, sptLookup]⟩
    exact ⟨addSpace { target with locals := env } amount, by simp [DataSem.evaluate, targetCut], nextRel, by simp [addSpace]⟩

/-- Return reads identical values and flushes locals on both sides. -/
theorem evaluatorSimulation_return {C F : Type} (names : List Nat) :
    evaluatorSimulation (C := C) (F := F) (.return names) := by
  intro source target sourceNext result related sameLocals exception notType run
  have readEq : DataSem.getVars names source.locals = DataSem.getVars names target.locals := by rw [sameLocals]
  cases read : DataSem.getVars names source.locals with
  | none =>
    have targetRead : DataSem.getVars names target.locals = none := by rw [← readEq, read]
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp [DataSem.evaluate, targetRead], related, by simp⟩
  | some values =>
    have targetRead : DataSem.getVars names target.locals = some values := by rw [← readEq, read]
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨flushState false target, by simp [DataSem.evaluate, targetRead], stateRel_flushLocals source target .ln related, by simp⟩

/-- Raise follows the supplied correspondence between exception jumps. -/
theorem evaluatorSimulation_raise {C F : Type} (name : Nat) :
    evaluatorSimulation (C := C) (F := F) (.raise name) := by
  intro source target sourceNext result related sameLocals exception notType run
  have readEq : DataSem.getVar name source.locals = DataSem.getVar name target.locals := by rw [sameLocals]
  cases read : DataSem.getVar name source.locals with
  | none =>
    have targetRead : DataSem.getVar name target.locals = none := by rw [← readEq, read]
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact ⟨target, by simp [DataSem.evaluate, targetRead], related, by simp⟩
  | some value =>
    have targetRead : DataSem.getVar name target.locals = some value := by rw [← readEq, read]
    cases jump : jumpExc source with
    | none =>
      simp [DataSem.evaluate, read, jump] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some sourceJump =>
      obtain ⟨targetJump, targetRun, jumpRel, _, _⟩ := exception sourceJump jump
      simp [DataSem.evaluate, read, jump] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨targetJump, by simp [DataSem.evaluate, targetRead, targetRun], jumpRel, by simp⟩

/-- The assignment case follows from the full primitive relation. -/
theorem evaluatorSimulation_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (args : List Nat) (names : Option NumSet) :
    evaluatorSimulation (C := C) (F := F) (.assign dest op args names) := by
  intro source target sourceNext result related sameLocals exception notType run
  exact evaluate_assign_sameLocals dest op args names source target sourceNext result related sameLocals run

end Flapjack.Compiler.Backend.DataLive

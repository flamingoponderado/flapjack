import Flapjack.Compiler.Backend.DataSpace.Proofs.State
import Flapjack.Compiler.Backend.Semantics.DataProps.Jump
import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock

/-! Basic cases of data-space reservation simulation. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Auxiliary simulation using sparse-tree inclusion for the target locals.
The source evaluator and carrier correspondence remain to be reviewed. -/
def simulationFor {C F : Type} (program : DataLang.Prog) : Prop :=
  ∀ (source sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value)) (locals : Spt DataSem.Value),
    result ≠ some (.err (.abort .typeError)) → DataSem.evaluate program source = (result, sourceNext) →
    sptSubspt source.locals locals →
    ∃ out safe peak stackMax,
      DataSem.evaluate (compile program) { source with locals := locals } =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt sourceNext.locals out

/-- Skip preserves the auxiliary reservation simulation. -/
theorem simulationFor_skip {C F : Type} : simulationFor (C := C) (F := F) .skip := by
  intro source sourceNext result locals notType run included
  simp [DataSem.evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  exact ⟨locals, source.safeForSpace, source.peakHeapLength, source.stackMax, by simp [compile, space, pMakeSpace, DataSem.evaluate], included⟩

/-- Moving a live local preserves sparse-tree extension. -/
theorem simulationFor_move {C F : Type} (dest src : Nat) : simulationFor (C := C) (F := F) (.move dest src) := by
  intro source sourceNext result locals notType run included
  cases read : DataSem.getVar src source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some value =>
    have targetRead : DataSem.getVar src locals = some value := (sptSubsptLookup _ _).1 included src value read
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨sptInsert dest value locals, source.safeForSpace, source.peakHeapLength, source.stackMax, ?_, ?_⟩
    · simp [compile, space, pMakeSpace, DataSem.evaluate, targetRead, setVar]
    · exact insert_subspt source.locals locals dest value included

/-- Clock ticks preserve local extension, including timeout. -/
theorem simulationFor_tick {C F : Type} : simulationFor (C := C) (F := F) .tick := by
  intro source sourceNext result locals notType run included
  by_cases zero : source.clock = 0
  · simp [DataSem.evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨.ln, source.safeForSpace, source.peakHeapLength, source.stackMax, ?_, ?_⟩
    · simp [compile, space, pMakeSpace, DataSem.evaluate, zero, flushState]
    · simp [flushState, sptSubspt, sptMem, sptDomain, sptLookup]
  · simp [DataSem.evaluate, zero] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨locals, source.safeForSpace, source.peakHeapLength, source.stackMax, ?_, ?_⟩
    · simp [compile, space, pMakeSpace, DataSem.evaluate, zero, decClock]
    · exact included

/-- A reservation cuts equal environments and applies the same accounting. -/
theorem simulationFor_makeSpace {C F : Type} (amount : Nat) (names : NumSet) :
    simulationFor (C := C) (F := F) (.makeSpace amount names) := by
  intro source sourceNext result locals notType run included
  cases cut : cutEnv names source.locals with
  | none =>
    simp [DataSem.evaluate, cut] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some env =>
    have targetCut := cutEnv_of_subspt names source.locals locals env included cut
    simp [DataSem.evaluate, cut] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨env, (addSpace { source with locals := env } amount).safeForSpace,
      (addSpace { source with locals := env } amount).peakHeapLength,
      (addSpace { source with locals := env } amount).stackMax, ?_, ?_⟩
    · change DataSem.evaluate (.seq (.makeSpace amount names) .skip) { source with locals := locals } = _
      rw [DataSem.evaluate_seq_skip]
      simp [DataSem.evaluate, targetCut, addSpace]
    · intro key member
      exact ⟨member, rfl⟩

/-- A value return reads the same values and flushes both environments. -/
theorem simulationFor_return {C F : Type} (names : List Nat) :
    simulationFor (C := C) (F := F) (.return names) := by
  intro source sourceNext result locals notType run included
  cases read : DataSem.getVars names source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some values =>
    have targetRead := getVars_of_subspt names source.locals locals values included read
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨.ln, source.safeForSpace, source.peakHeapLength, source.stackMax, ?_, ?_⟩
    · simp [compile, space, pMakeSpace, DataSem.evaluate, targetRead, flushState]
    · simp [flushState, sptSubspt, sptMem, sptDomain, sptLookup]

/-- An exception jump restores its saved locals regardless of the current
local environment. -/
theorem simulationFor_raise {C F : Type} (name : Nat) :
    simulationFor (C := C) (F := F) (.raise name) := by
  intro source sourceNext result locals notType run included
  cases read : DataSem.getVar name source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some value =>
    have targetRead : DataSem.getVar name locals = some value := (sptSubsptLookup _ _).1 included name value read
    cases jump : jumpExc source with
    | none =>
      simp [DataSem.evaluate, read, jump] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some jumped =>
      have targetJump : jumpExc { source with locals := locals } = some jumped := by
        have moved := jumpExc_transport source { source with locals := locals } jumped rfl rfl jump
        have shape := Option.some.inj (jump.symm.trans (jumpExc_transport source source jumped rfl rfl jump))
        simpa [← shape] using moved
      simp [DataSem.evaluate, read, jump] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨jumped.locals, jumped.safeForSpace, jumped.peakHeapLength, jumped.stackMax, ?_, ?_⟩
      · simp [compile, space, pMakeSpace, DataSem.evaluate, targetRead, targetJump]
      · intro key member
        exact ⟨member, rfl⟩

end Flapjack.Compiler.Backend.DataSpace

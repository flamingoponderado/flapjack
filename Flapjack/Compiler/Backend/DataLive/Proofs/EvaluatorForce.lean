module

public import Flapjack.Compiler.Backend.DataLive.Proofs.CallHandler

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.BviSem.Evaluate
import all Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
@[expose] public section

/-! Same-program force simulation across related call stacks. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A running non-tail force preserves same-program simulation when the
smaller-clock evaluator hypothesis is available. -/
theorem evaluatorSimulation_force_nonTail_running_at {C F : Type} (dest : Nat) (names : NumSet)
    (label src : Nat) (source target sourceNext : State C F)
    (result : Option (Result (List DataSem.Value) DataSem.Value)) (thunk function : DataSem.Value)
    (related : stateRel source target .ln) (sameLocals : source.locals = target.locals)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (run : DataSem.evaluate (.force (some (dest, names)) label src) source = (result, sourceNext))
    (read : getVar src source.locals = some thunk)
    (unevaluated : destThunk thunk source.refs = .isThunk .notEvaluated function)
    (nonzero : source.clock ≠ 0) (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (.force (some (dest, names)) label src) target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals) := by
  have targetRead : getVar src target.locals = some thunk := by rw [← sameLocals, read]
  have targetThunk : destThunk thunk target.refs = .isThunk .notEvaluated function := by
    rw [← related.2.2.2.2.1, unevaluated]
  have targetNonzero : target.clock ≠ 0 := by rw [← related.2.1]; exact nonzero
  have findEq : findCode (some label) [thunk, function] target.code target.stackFrameSizes =
      findCode (some label) [thunk, function] source.code source.stackFrameSizes := by
    rw [← related.1, ← related.2.2.2.2.2.2.2.2.2.2.2.2.1]
  cases found : findCode (some label) [thunk, function] source.code source.stackFrameSizes with
  | none =>
    simp [DataSem.evaluate, read, unevaluated, found] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some triple =>
    obtain ⟨args, body, size⟩ := triple
    have targetFound : findCode (some label) [thunk, function] target.code target.stackFrameSizes = some (args, body, size) := by rw [findEq, found]
    cases cut : cutEnv names source.locals with
    | none =>
      simp [DataSem.evaluate, read, unevaluated, found, cut] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some env =>
      have targetCut : cutEnv names target.locals = some env := by rw [← sameLocals, cut]
      have savedRel : stateRel { source with locals := env } { target with locals := env } .ln := by
        rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
        exact ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, by simp⟩
      let sourceEntry := DataSem.callEnv args size (pushEnv env false (decClock source))
      let targetEntry := DataSem.callEnv args size (pushEnv env false (decClock target))
      have entryRel := stateRel_nonTailEntry source target .ln args size env env false related
      have entryException := exceptionRel_nonTailEntry_noHandler source target .ln args size env env related exception
      have smaller : sourceEntry.clock < source.clock := by
        simp [sourceEntry, DataSem.callEnv, pushEnv, decClock]
        omega
      cases called : DataSem.evaluate body sourceEntry with
      | mk outcome last =>
        have sourceClamped : fixClock sourceEntry (DataSem.evaluate body sourceEntry) = (outcome, last) := by
          rw [fixClock_evaluate, called]
        simp only [sourceEntry] at sourceClamped
        cases outcome with
        | none =>
          simp [DataSem.evaluate, read, unevaluated, found, cut, nonzero, sourceClamped] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)
        | some outcome =>
          cases outcome with
          | err error =>
            simp [DataSem.evaluate, read, unevaluated, found, cut, nonzero, sourceClamped] at run
            obtain ⟨rfl, rfl⟩ := run
            obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
              bodyIH body sourceEntry targetEntry last (some (.err error)) smaller entryRel.1 entryRel.2 entryException notType called
            have targetClamped := targetRun
            rw [← fixClock_evaluate body targetEntry] at targetClamped
            simp only [targetEntry] at targetClamped
            exact ⟨targetLast, by simp [DataSem.evaluate, targetRead, targetThunk, targetFound, targetCut, targetNonzero, targetClamped], lastRel, by simp⟩
          | val values =>
            cases values with
            | nil =>
              simp [DataSem.evaluate, read, unevaluated, found, cut, nonzero, sourceClamped] at run
              obtain ⟨rfl, rfl⟩ := run
              exact False.elim (notType rfl)
            | cons value rest =>
              cases rest with
              | cons other rest =>
                simp [DataSem.evaluate, read, unevaluated, found, cut, nonzero, sourceClamped] at run
                obtain ⟨rfl, rfl⟩ := run
                exact False.elim (notType rfl)
              | nil =>
                obtain ⟨targetLast, targetRun, lastRel, _⟩ :=
                  bodyIH body sourceEntry targetEntry last (some (.val [value])) smaller entryRel.1 entryRel.2 entryException (by simp) called
                have sourceControl := evaluate_stackResult body sourceEntry last (some (.val [value])) called
                have targetControl := evaluate_stackResult body targetEntry targetLast (some (.val [value])) targetRun
                obtain ⟨sourcePop, targetPop, sourcePopRun, targetPopRun, popRel⟩ :=
                  stateRel_popNonTail source target last targetLast args size env env false .ln
                    lastRel savedRel sourceControl.1 sourceControl.2 targetControl.1 targetControl.2
                have sourcePopLocals := popNonTail_locals source last sourcePop args size env false sourceControl.1 sourceControl.2 sourcePopRun
                have targetPopLocals := popNonTail_locals target targetLast targetPop args size env false targetControl.1 targetControl.2 targetPopRun
                simp [DataSem.evaluate, read, unevaluated, found, cut, nonzero, sourceClamped, sourcePopRun] at run
                obtain ⟨rfl, rfl⟩ := run
                have targetClamped : fixClock targetEntry (DataSem.evaluate body targetEntry) = (some (.val [value]), targetLast) := by
                  rw [fixClock_evaluate, targetRun]
                simp only [targetEntry] at targetClamped
                have afterRel : stateRel (setVar dest value sourcePop) (setVar dest value targetPop) .ln :=
                  stateRel_setVar sourcePop targetPop .ln dest value (by simpa [sptDelete] using popRel)
                refine ⟨setVar dest value targetPop, ?_, afterRel, ?_⟩
                · simp [DataSem.evaluate, targetRead, targetThunk, targetFound, targetCut, targetNonzero, targetClamped, targetPopRun]
                · intro _
                  simp [setVar, sourcePopLocals, targetPopLocals]

/-- Same-program force simulation at one clock, conditional only on the
same-program evaluator induction hypothesis at smaller clocks. -/
theorem evaluatorSimulation_force_at {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (related : stateRel source target .ln) (sameLocals : source.locals = target.locals)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (run : DataSem.evaluate (.force ret label src) source = (result, sourceNext))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (.force ret label src) target = (result, targetNext) ∧
      stateRel sourceNext targetNext .ln ∧ (result = none → sourceNext.locals = targetNext.locals) := by
  cases ret with
  | none => exact evaluatorSimulation_tailForce_at label src source target sourceNext result related sameLocals exception notType run bodyIH
  | some pair =>
    obtain ⟨dest, names⟩ := pair
    cases read : getVar src source.locals with
    | none =>
      simp [DataSem.evaluate, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some thunk =>
      have targetRead : getVar src target.locals = some thunk := by rw [← sameLocals, read]
      cases inspect : destThunk thunk source.refs with
      | badRef =>
        simp [DataSem.evaluate, read, inspect] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | notThunk =>
        simp [DataSem.evaluate, read, inspect] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | isThunk mode value =>
        have targetInspect : destThunk thunk target.refs = .isThunk mode value := by rw [← related.2.2.2.2.1, inspect]
        cases mode with
        | evaluated =>
          cases cut : cutEnv names source.locals with
          | none =>
            simp [DataSem.evaluate, read, inspect, cut] at run
            obtain ⟨rfl, rfl⟩ := run
            exact False.elim (notType rfl)
          | some env =>
            have targetCut : cutEnv names target.locals = some env := by rw [← sameLocals, cut]
            simp [DataSem.evaluate, read, inspect, cut] at run
            obtain ⟨rfl, rfl⟩ := run
            have cutRel : stateRel { source with locals := env } { target with locals := env } (sptDelete dest .ln) := by
              rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
              exact ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, by simp⟩
            refine ⟨setVar dest value { target with locals := env }, ?_, stateRel_setVar _ _ .ln dest value cutRel, ?_⟩
            · simp [DataSem.evaluate, targetRead, targetInspect, targetCut]
            · simp [setVar]
        | notEvaluated =>
          by_cases zero : source.clock = 0
          · have targetZero : target.clock = 0 := by rw [← related.2.1, zero]
            have findEq : findCode (some label) [thunk, value] target.code target.stackFrameSizes =
                findCode (some label) [thunk, value] source.code source.stackFrameSizes := by
              rw [← related.1, ← related.2.2.2.2.2.2.2.2.2.2.2.2.1]
            cases found : findCode (some label) [thunk, value] source.code source.stackFrameSizes with
            | none =>
              simp [DataSem.evaluate, read, inspect, found] at run
              obtain ⟨rfl, rfl⟩ := run
              exact False.elim (notType rfl)
            | some triple =>
              obtain ⟨args, body, size⟩ := triple
              have targetFound : findCode (some label) [thunk, value] target.code target.stackFrameSizes = some (args, body, size) := by rw [findEq, found]
              cases cut : cutEnv names source.locals with
              | none =>
                simp [DataSem.evaluate, read, inspect, found, cut] at run
                obtain ⟨rfl, rfl⟩ := run
                exact False.elim (notType rfl)
              | some env =>
                have targetCut : cutEnv names target.locals = some env := by rw [← sameLocals, cut]
                simp [DataSem.evaluate, read, inspect, found, cut, zero] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨{ (DataSem.callEnv args size (pushEnv env false (decClock target))) with stack := [], locals := .ln }, ?_, ?_, by simp⟩
                · simp [DataSem.evaluate, targetRead, targetInspect, targetFound, targetCut, targetZero]
                · exact stateRel_forceTimeoutCall source target .ln args size env env related
          · exact evaluatorSimulation_force_nonTail_running_at dest names label src source target sourceNext result thunk value
              related sameLocals exception notType run read inspect zero bodyIH

end Flapjack.Compiler.Backend.DataLive

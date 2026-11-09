module

public import Flapjack.Compiler.Backend.DataLive.Proofs.CallFrame

@[expose] public section

/-! Non-tail force simulation with the evaluator induction hypothesis. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A running non-tail force simulates once same-program evaluation is
known at smaller clocks. The evaluator induction hypothesis remains open. -/
theorem force_nonTail_running_correct {C F : Type} (dest : Nat) (names : NumSet) (label src : Nat) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (thunk function : DataSem.Value)
    (run : DataSem.evaluate (.force (some (dest, names)) label src) source = (result, sourceNext))
    (related : stateRel source target (compile (.force (some (dest, names)) label src) live).2)
    (exception : exceptionRel source target) (notType : result ≠ some (.err (.abort .typeError)))
    (read : DataSem.getVar src source.locals = some thunk)
    (unevaluated : destThunk thunk source.refs = .isThunk .notEvaluated function)
    (nonzero : source.clock ≠ 0) (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (compile (.force (some (dest, names)) label src) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  have initial : stateRel source target (sptInsert src () (sptInter names (sptDelete dest live))) := by simpa [compile] using related
  have srcLive : sptMem src (sptInsert src () (sptInter names (sptDelete dest live))) :=
    (sptMem_sptInsert src src () _).2 (Or.inl rfl)
  have readEq := stateRel_getVar source target _ src initial srcLive
  have targetRead : DataSem.getVar src target.locals = some thunk := by rw [← readEq, read]
  have refs := initial.2.2.2.2.1
  have targetThunk : destThunk thunk target.refs = .isThunk .notEvaluated function := by rw [← refs, unevaluated]
  have targetNonzero : target.clock ≠ 0 := by rw [← initial.2.1]; exact nonzero
  have findEq : findCode (some label) [thunk, function] target.code target.stackFrameSizes =
      findCode (some label) [thunk, function] source.code source.stackFrameSizes := by
    rw [← initial.1, ← initial.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have cutRel : stateRel source target (sptInter names (sptDelete dest live)) :=
    stateRel_mono source target _ _ initial (fun key member => (sptMem_sptInsert key src () _).2 (Or.inr member))
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
    | some sourceEnv =>
      obtain ⟨targetEnv, targetCut, savedLocals⟩ := cutEnv_inter_related source target names (sptDelete dest live) cutRel sourceEnv cut
      have savedRel : stateRel { source with locals := sourceEnv } { target with locals := targetEnv } (sptDelete dest live) := by
        rcases initial with ⟨code, clock, space, ffi, refEq, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
        exact ⟨code, clock, space, ffi, refEq, global, handler, stack, compiler, oracle, stamps, limits, frames, savedLocals⟩
      let sourceEntry := DataSem.callEnv args size (pushEnv sourceEnv false (decClock source))
      let targetEntry := DataSem.callEnv args size (pushEnv targetEnv false (decClock target))
      have entryRel := stateRel_nonTailEntry source target _ args size sourceEnv targetEnv false initial
      have entryException := exceptionRel_nonTailEntry_noHandler source target _ args size sourceEnv targetEnv initial exception
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
            refine ⟨targetLast, ?_, lastRel⟩
            have targetClamped : fixClock targetEntry (DataSem.evaluate body targetEntry) = (some (.err error), targetLast) := by
              rw [fixClock_evaluate, targetRun]
            simp only [targetEntry] at targetClamped
            simp [compile, DataSem.evaluate, targetRead, targetThunk, targetFound, targetCut, targetNonzero, targetClamped]
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
                  stateRel_popNonTail source target last targetLast args size sourceEnv targetEnv false (sptDelete dest live)
                    lastRel savedRel sourceControl.1 sourceControl.2 targetControl.1 targetControl.2
                simp [DataSem.evaluate, read, unevaluated, found, cut, nonzero, sourceClamped, sourcePopRun] at run
                obtain ⟨rfl, rfl⟩ := run
                refine ⟨setVar dest value targetPop, ?_, stateRel_setVar sourcePop targetPop live dest value popRel⟩
                have targetClamped : fixClock targetEntry (DataSem.evaluate body targetEntry) = (some (.val [value]), targetLast) := by
                  rw [fixClock_evaluate, targetRun]
                simp only [targetEntry] at targetClamped
                simp [compile, DataSem.evaluate, targetRead, targetThunk, targetFound, targetCut, targetNonzero, targetClamped, targetPopRun]

/-- All force cases, conditional on same-program simulation at smaller clocks. -/
theorem force_correct_at {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (run : DataSem.evaluate (.force ret label src) source = (result, sourceNext))
    (related : stateRel source target (compile (.force ret label src) live).2)
    (exception : exceptionRel source target)
    (notType : result ≠ some (.err (.abort .typeError)))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (compile (.force ret label src) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  cases ret with
  | none => exact force_tail_correct label src live source target sourceNext result run related exception notType bodyIH
  | some pair =>
    obtain ⟨dest, names⟩ := pair
    cases read : DataSem.getVar src source.locals with
    | none =>
      simp [DataSem.evaluate, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some thunk =>
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
        cases mode with
        | evaluated => exact force_evaluated_correct (some (dest, names)) label src live source target sourceNext result thunk value run related notType read inspect
        | notEvaluated =>
          by_cases zero : source.clock = 0
          · exact force_timeout_correct (some (dest, names)) label src live source target sourceNext result thunk value run related notType read inspect zero
          · exact force_nonTail_running_correct dest names label src live source target sourceNext result thunk value run related exception notType read inspect zero bodyIH

end Flapjack.Compiler.Backend.DataLive

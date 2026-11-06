import Flapjack.Compiler.Backend.Semantics.DataProps.CallEntry

/-! Tail-force liveness simulation with the evaluator induction hypothesis. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A tail force of an unevaluated thunk simulates once same-program
evaluation is known at smaller clocks. The induction hypothesis is an open
prerequisite; this is not yet the complete HOL force case. -/
theorem force_tail_running_correct {C F : Type} (label src : Nat) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (thunk function : DataSem.Value)
    (run : DataSem.evaluate (.force none label src) source = (result, sourceNext))
    (related : stateRel source target (compile (.force none label src) live).2)
    (exception : exceptionRel source target)
    (notType : result ≠ some (.err (.abort .typeError)))
    (read : DataSem.getVar src source.locals = some thunk)
    (unevaluated : destThunk thunk source.refs = .isThunk .notEvaluated function)
    (nonzero : source.clock ≠ 0)
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (compile (.force none label src) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  have initial : stateRel source target (sptInsert src () .ln) := by simpa [compile] using related
  have srcLive : sptMem src (sptInsert src () .ln) := (sptMem_sptInsert src src () _).2 (Or.inl rfl)
  have readEq := stateRel_getVar source target _ src initial srcLive
  have targetRead : DataSem.getVar src target.locals = some thunk := by rw [← readEq, read]
  have refs := initial.2.2.2.2.1
  have targetThunk : destThunk thunk target.refs = .isThunk .notEvaluated function := by rw [← refs, unevaluated]
  have targetNonzero : target.clock ≠ 0 := by rw [← initial.2.1]; exact nonzero
  have findEq : findCode (some label) [thunk, function] target.code target.stackFrameSizes =
      findCode (some label) [thunk, function] source.code source.stackFrameSizes := by
    rw [← initial.1, ← initial.2.2.2.2.2.2.2.2.2.2.2.2.1]
  cases found : findCode (some label) [thunk, function] source.code source.stackFrameSizes with
  | none =>
    simp [DataSem.evaluate, read, unevaluated, found] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some triple =>
    obtain ⟨args, body, size⟩ := triple
    have targetFound : findCode (some label) [thunk, function] target.code target.stackFrameSizes = some (args, body, size) := by rw [findEq, found]
    let sourceEntry := DataSem.callEnv args size (decClock source)
    let targetEntry := DataSem.callEnv args size (decClock target)
    have entryRel := stateRel_tailEntry source target _ args size initial
    have entryException := exceptionRel_tailEntry source target _ args size initial exception
    have smaller : sourceEntry.clock < source.clock := by
      simp [sourceEntry, DataSem.callEnv, decClock]
      omega
    cases called : DataSem.evaluate body sourceEntry with
    | mk outcome last =>
      have calledUnfolded := called
      simp only [sourceEntry] at calledUnfolded
      cases outcome with
      | none =>
        simp [DataSem.evaluate, read, unevaluated, found, nonzero, calledUnfolded] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | some value =>
        simp [DataSem.evaluate, read, unevaluated, found, nonzero, calledUnfolded] at run
        obtain ⟨rfl, rfl⟩ := run
        obtain ⟨targetNext, targetRun, nextRel, _⟩ :=
          bodyIH body sourceEntry targetEntry last (some value) smaller entryRel.1 entryRel.2 entryException notType called
        refine ⟨targetNext, ?_, nextRel⟩
        simp only [targetEntry] at targetRun
        simp [compile, DataSem.evaluate, targetRead, targetThunk, targetFound, targetNonzero, targetRun]

/-- Tail force simulates for evaluated thunks, timeouts, and running
thunks, assuming same-program evaluation at smaller clocks. -/
theorem force_tail_correct {C F : Type} (label src : Nat) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (run : DataSem.evaluate (.force none label src) source = (result, sourceNext))
    (related : stateRel source target (compile (.force none label src) live).2)
    (exception : exceptionRel source target)
    (notType : result ≠ some (.err (.abort .typeError)))
    (bodyIH : evaluatorSimulationBelow (C := C) (F := F) source.clock) :
    ∃ targetNext, DataSem.evaluate (compile (.force none label src) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
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
      | evaluated => exact force_evaluated_correct none label src live source target sourceNext result thunk value run related notType read inspect
      | notEvaluated =>
        by_cases zero : source.clock = 0
        · exact force_timeout_correct none label src live source target sourceNext result thunk value run related notType read inspect zero
        · exact force_tail_running_correct label src live source target sourceNext result thunk value run related exception notType read inspect zero bodyIH

end Flapjack.Compiler.Backend.DataLive

module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveMemoryUpdate

@[expose] public section

/-! Forced-thunk cases of data liveness simulation. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Flushing locals without dropping the stack preserves related observable
fields at an empty live set. -/
theorem stateRel_flushLocals {C F : Type} (source target : State C F) (live : NumSet)
    (related : stateRel source target live) : stateRel (flushState false source) (flushState false target) .ln := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
  refine ⟨code, clock, space, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, ?_⟩
  intro key member
  simp [sptMem, sptDomain, sptLookup] at member

/-- A force of an already evaluated thunk is simulated for either return
form. The not-yet-evaluated thunk cases remain open; this case is untagged
pending source evaluator and state-carrier review. -/
theorem force_evaluated_correct {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (thunk value : DataSem.Value)
    (run : DataSem.evaluate (.force ret label src) source = (result, sourceNext))
    (related : stateRel source target (compile (.force ret label src) live).2)
    (notType : result ≠ some (.err (.abort .typeError)))
    (read : DataSem.getVar src source.locals = some thunk)
    (evaluated : destThunk thunk source.refs = .isThunk .evaluated value) :
    ∃ targetNext, DataSem.evaluate (compile (.force ret label src) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  cases ret with
  | none =>
    have initial : stateRel source target (sptInsert src () .ln) := by simpa [compile] using related
    have srcLive : sptMem src (sptInsert src () .ln) := (sptMem_sptInsert src src () _).2 (Or.inl rfl)
    have readEq := stateRel_getVar source target _ src initial srcLive
    have targetRead : DataSem.getVar src target.locals = some thunk := by rw [← readEq, read]
    have refs := initial.2.2.2.2.1
    have targetEvaluated : destThunk thunk target.refs = .isThunk .evaluated value := by rw [← refs, evaluated]
    simp [DataSem.evaluate, read, evaluated] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨flushState false target, ?_, stateRel_flushLocals source target _ initial⟩
    simp [compile, DataSem.evaluate, targetRead, targetEvaluated]
  | some pair =>
    obtain ⟨dest, names⟩ := pair
    have initial : stateRel source target (sptInsert src () (sptInter names (sptDelete dest live))) := by
      simpa [compile] using related
    have srcLive : sptMem src (sptInsert src () (sptInter names (sptDelete dest live))) :=
      (sptMem_sptInsert src src () _).2 (Or.inl rfl)
    have readEq := stateRel_getVar source target _ src initial srcLive
    have targetRead : DataSem.getVar src target.locals = some thunk := by rw [← readEq, read]
    have refs := initial.2.2.2.2.1
    have targetEvaluated : destThunk thunk target.refs = .isThunk .evaluated value := by rw [← refs, evaluated]
    have cutRel : stateRel source target (sptInter names (sptDelete dest live)) :=
      stateRel_mono source target _ _ initial (fun key member => (sptMem_sptInsert key src () _).2 (Or.inr member))
    cases cut : cutEnv names source.locals with
    | none =>
      simp [DataSem.evaluate, read, evaluated, cut] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some sourceEnv =>
      obtain ⟨targetEnv, targetCut, locals⟩ :=
        cutEnv_inter_related source target names (sptDelete dest live) cutRel sourceEnv cut
      have cutRelated : stateRel { source with locals := sourceEnv } { target with locals := targetEnv }
          (sptDelete dest live) := by
        rcases initial with ⟨code, clock, space, ffi, refEq, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
        exact ⟨code, clock, space, ffi, refEq, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
      simp [DataSem.evaluate, read, evaluated, cut] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨setVar dest value { target with locals := targetEnv }, ?_, ?_⟩
      · simp [compile, DataSem.evaluate, targetRead, targetEvaluated, targetCut]
      · exact stateRel_setVar _ _ live dest value cutRelated

/-- Clearing both stacks and locals preserves related observable fields. -/
theorem stateRel_clearStackLocals {C F : Type} (source target : State C F) (live : NumSet)
    (related : stateRel source target live) :
    stateRel { source with stack := [], locals := .ln } { target with stack := [], locals := .ln } .ln := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, _, compiler, oracle, stamps, limits, frames, _⟩
  refine ⟨code, clock, space, ffi, refs, global, handler, rfl, compiler, oracle, stamps, limits, frames, ?_⟩
  intro key member
  simp [sptMem, sptDomain, sptLookup] at member

/-- A timed-out non-tail call preserves the relation after discarding its
fresh frame, regardless of the saved environments. -/
theorem stateRel_forceTimeoutCall {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (size : Option Nat) (sourceEnv targetEnv : Spt DataSem.Value)
    (related : stateRel source target live) :
    stateRel { (DataSem.callEnv args size (pushEnv sourceEnv false (decClock source))) with stack := [], locals := .ln }
      { (DataSem.callEnv args size (pushEnv targetEnv false (decClock target))) with stack := [], locals := .ln } .ln := by
  rcases related with ⟨code, clock, space, ffi, refs, global, handler, _, compiler, oracle, stamps, limits, frames, _⟩
  simp [stateRel, DataSem.callEnv, pushEnv, decClock, code, clock, space, ffi, refs, global, handler,
    compiler, oracle, stamps, limits, frames, sptMem, sptDomain, sptLookup]

/-- Forcing an unevaluated thunk at clock zero is simulated for either
return form. This is an untagged source case, not the full force theorem. -/
theorem force_timeout_correct {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat) (live : NumSet)
    (source target sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (thunk function : DataSem.Value)
    (run : DataSem.evaluate (.force ret label src) source = (result, sourceNext))
    (related : stateRel source target (compile (.force ret label src) live).2)
    (notType : result ≠ some (.err (.abort .typeError)))
    (read : DataSem.getVar src source.locals = some thunk)
    (unevaluated : destThunk thunk source.refs = .isThunk .notEvaluated function)
    (zero : source.clock = 0) :
    ∃ targetNext, DataSem.evaluate (compile (.force ret label src) live).1 target = (result, targetNext) ∧
      stateRel sourceNext targetNext (postLive result live) := by
  cases ret with
  | none =>
    have initial : stateRel source target (sptInsert src () .ln) := by simpa [compile] using related
    have srcLive : sptMem src (sptInsert src () .ln) := (sptMem_sptInsert src src () _).2 (Or.inl rfl)
    have readEq := stateRel_getVar source target _ src initial srcLive
    have targetRead : DataSem.getVar src target.locals = some thunk := by rw [← readEq, read]
    have refs := initial.2.2.2.2.1
    have targetThunk : destThunk thunk target.refs = .isThunk .notEvaluated function := by rw [← refs, unevaluated]
    have targetZero : target.clock = 0 := by rw [← initial.2.1, zero]
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
      simp [DataSem.evaluate, read, unevaluated, found, zero] at run
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨{ target with stack := [], locals := .ln }, ?_, ?_⟩
      · simp [compile, DataSem.evaluate, targetRead, targetThunk, targetFound, targetZero]
      · simpa [zero, postLive] using stateRel_clearStackLocals source target _ initial
  | some pair =>
    obtain ⟨dest, names⟩ := pair
    have initial : stateRel source target (sptInsert src () (sptInter names (sptDelete dest live))) := by simpa [compile] using related
    have srcLive : sptMem src (sptInsert src () (sptInter names (sptDelete dest live))) :=
      (sptMem_sptInsert src src () _).2 (Or.inl rfl)
    have readEq := stateRel_getVar source target _ src initial srcLive
    have targetRead : DataSem.getVar src target.locals = some thunk := by rw [← readEq, read]
    have refs := initial.2.2.2.2.1
    have targetThunk : destThunk thunk target.refs = .isThunk .notEvaluated function := by rw [← refs, unevaluated]
    have targetZero : target.clock = 0 := by rw [← initial.2.1, zero]
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
        obtain ⟨targetEnv, targetCut, _⟩ := cutEnv_inter_related source target names (sptDelete dest live) cutRel sourceEnv cut
        simp [DataSem.evaluate, read, unevaluated, found, cut, zero] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨{ (DataSem.callEnv args size (pushEnv targetEnv false (decClock target))) with stack := [], locals := .ln }, ?_, ?_⟩
        · simp [compile, DataSem.evaluate, targetRead, targetThunk, targetFound, targetCut, targetZero]
        · simpa [zero, postLive, DataSem.callEnv, pushEnv, decClock] using
            stateRel_forceTimeoutCall source target _ args size sourceEnv targetEnv initial

end Flapjack.Compiler.Backend.DataLive

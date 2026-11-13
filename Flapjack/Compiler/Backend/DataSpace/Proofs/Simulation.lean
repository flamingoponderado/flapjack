module

public import Flapjack.Compiler.Backend.DataSpace.Proofs.State
public import Flapjack.Compiler.Backend.Semantics.DataProps.Jump
public import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock
public import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveAll
public import Flapjack.Compiler.Backend.DataLive.Proofs.CompileCorrect

@[expose] public section

/-! Basic cases of data-space reservation simulation. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.DataProps Flapjack.SemanticPrimitivesHOL

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

/-- An identical target evaluation immediately supplies the reservation
simulation witness. -/
theorem simulationWitness_of_equal {C F : Type} (program : DataLang.Prog)
    (source sourceNext : State C F) (result : Option (Result (List DataSem.Value) DataSem.Value))
    (locals : Spt DataSem.Value)
    (run : DataSem.evaluate program { source with locals := locals } = (result, sourceNext)) :
    ∃ out safe peak stackMax,
      DataSem.evaluate program { source with locals := locals } =
        (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
          else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) ∧
      sptSubspt sourceNext.locals out := by
  refine ⟨sourceNext.locals, sourceNext.safeForSpace, sourceNext.peakHeapLength, sourceNext.stackMax, ?_, ?_⟩
  · simpa using run
  · intro key member
    exact ⟨member, rfl⟩

/-- Callee entry overwrites the caller locals. -/
theorem callEnv_changeLocals {C F : Type} (source : State C F) (locals : Spt DataSem.Value)
    (args : List DataSem.Value) (size : Option Nat) :
    DataSem.callEnv args size (decClock { source with locals := locals }) = DataSem.callEnv args size (decClock source) := by
  rfl

/-- Saving an explicit environment before callee entry also makes the
original caller locals irrelevant. -/
theorem callEnv_push_changeLocals {C F : Type} (source : State C F) (locals env : Spt DataSem.Value)
    (args : List DataSem.Value) (size : Option Nat) (handler : Bool) :
    DataSem.callEnv args size (pushEnv env handler (decClock { source with locals := locals })) =
      DataSem.callEnv args size (pushEnv env handler (decClock source)) := by
  cases handler <;> rfl

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

/-- An annotated assignment cuts the two environments to the same tree, so
the rest of the primitive evaluation starts from exactly the same state. -/
theorem simulationFor_annotatedAssign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (arguments : List Nat) (names : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest op arguments (some names)) := by
  intro source sourceNext result locals notType run included
  by_cases invalid : DataLang.opRequiresNames op = false
  · simp [DataSem.evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  · cases read : DataSem.getVars arguments source.locals with
    | none =>
      simp [DataSem.evaluate, invalid, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some values =>
      have targetRead := getVars_of_subspt arguments source.locals locals values included read
      cases cut : cutEnv names source.locals with
      | none =>
        simp [DataSem.evaluate, invalid, read, cutStateOpt, cutState, cut] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | some env =>
        have targetCut := cutEnv_of_subspt names source.locals locals env included cut
        have same : DataSem.evaluate (.assign dest op arguments (some names)) { source with locals := locals } =
            DataSem.evaluate (.assign dest op arguments (some names)) source := by
          simp [DataSem.evaluate, invalid, read, targetRead, cutStateOpt, cutState, cut, targetCut]
        refine ⟨sourceNext.locals, sourceNext.safeForSpace, sourceNext.peakHeapLength, sourceNext.stackMax, ?_, ?_⟩
        · simpa [compile, space, pMakeSpace] using same.trans run
        · intro key member
          exact ⟨member, rfl⟩

/-- An unannotated assignment preserves the simulation when the target has
additional locals; primitive accounting may change the three resource fields. -/
theorem simulationFor_unannotatedAssign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (arguments : List Nat) : simulationFor (C := C) (F := F) (.assign dest op arguments none) := by
  intro source sourceNext result locals notType run included
  by_cases invalid : DataLang.opRequiresNames op = true
  · simp [DataSem.evaluate, invalid] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  · cases read : DataSem.getVars arguments source.locals with
    | none =>
      simp [DataSem.evaluate, invalid, read] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some values =>
      have targetRead := getVars_of_subspt arguments source.locals locals values included read
      let target := { source with locals := locals }
      have related : DataLive.stateRel source target .ln := by
        rcases DataLive.stateRel_refl source .ln with ⟨code, clock, spaceEq, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, _⟩
        exact ⟨code, clock, spaceEq, ffi, refs, global, handler, stack, compiler, oracle, stamps, limits, frames, by simp [sptMem, sptDomain, sptLookup]⟩
      cases app : doApp op values source with
      | err error =>
        have targetApp := DataLive.stateRel_doApp_error source target .ln op values error related app
        simp [DataSem.evaluate, invalid, read, cutStateOpt, app] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨.ln, (installSfs op source).safeForSpace, source.peakHeapLength, source.stackMax, ?_, ?_⟩
        · simp [compile, space, pMakeSpace, DataSem.evaluate, invalid, targetRead, cutStateOpt, targetApp, target, flushState, installSfs]
        · simp [flushState, sptSubspt, sptMem, sptDomain, sptLookup]
      | val pair =>
        obtain ⟨value, sourceApplied⟩ := pair
        obtain ⟨targetApplied, targetApp, appRel⟩ :=
          DataLive.stateRel_doApp_success source target sourceApplied .ln op values value related app
        have sourceControl := doApp_control op values source sourceApplied value app
        have targetControl := doApp_control op values target targetApplied value targetApp
        have stateEq : targetApplied = { sourceApplied with locals := locals, safeForSpace := targetApplied.safeForSpace, peakHeapLength := targetApplied.peakHeapLength, stackMax := targetApplied.stackMax } := by
          rcases appRel with ⟨code, clock, spaceEq, ffi, refs, global, handler, _, compiler, oracle, stamps, limits, frames, _⟩
          cases sourceApplied
          cases targetApplied
          simp_all [target]
        simp [DataSem.evaluate, invalid, read, cutStateOpt, app] at run
        obtain ⟨rfl, rfl⟩ := run
        refine ⟨sptInsert dest value locals, (installSfs op targetApplied).safeForSpace,
          targetApplied.peakHeapLength, targetApplied.stackMax, ?_, ?_⟩
        · simp only [compile, space, pMakeSpace]
          simp [DataSem.evaluate, invalid, targetRead, cutStateOpt, targetApp, target]
          rw [stateEq]
          simp [setVar, installSfs]
        · simpa [setVar, installSfs, sourceControl.1] using insert_subspt source.locals locals dest value included

/-- Both assignment forms satisfy the data-space simulation. -/
theorem simulationFor_assign {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (arguments : List Nat) (names : Option NumSet) :
    simulationFor (C := C) (F := F) (.assign dest op arguments names) := by
  cases names with
  | none => exact simulationFor_unannotatedAssign dest op arguments
  | some names => exact simulationFor_annotatedAssign dest op arguments names

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

/-- Calls use identical callee states after reading their arguments and,
for non-tail calls, cutting the explicit saved environment. -/
theorem simulationFor_call {C F : Type} (ret : Option (List Nat × NumSet)) (dest : Option Nat)
    (arguments : List Nat) (handler : Option (Nat × DataLang.Prog)) :
    simulationFor (C := C) (F := F) (.call ret dest arguments handler) := by
  intro source sourceNext result locals notType run included
  cases read : DataSem.getVars arguments source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some values =>
    have targetRead := getVars_of_subspt arguments source.locals locals values included read
    cases found : findCode dest values source.code source.stackFrameSizes with
    | none =>
      simp [DataSem.evaluate, read, found] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some triple =>
      obtain ⟨args, body, size⟩ := triple
      cases ret with
      | none =>
        cases handler with
        | some pair =>
          simp [DataSem.evaluate, read, found] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)

        | none =>
          have same : DataSem.evaluate (.call none dest arguments none) { source with locals := locals } =
              DataSem.evaluate (.call none dest arguments none) source := by
            by_cases zero : source.clock = 0
            · simp [DataSem.evaluate, read, targetRead, found, zero, flushState]
            · simp [DataSem.evaluate, read, targetRead, found, zero, callEnv_changeLocals]
          simpa [compile, space, pMakeSpace] using
            simulationWitness_of_equal (.call none dest arguments none) source sourceNext result locals (same.trans run)
      | some pair =>
        obtain ⟨returns, names⟩ := pair
        by_cases unique : returns.Nodup
        · cases cut : cutEnv names source.locals with
          | none =>
            simp [DataSem.evaluate, read, found, unique, cut] at run
            obtain ⟨rfl, rfl⟩ := run
            exact False.elim (notType rfl)
          | some env =>
            have targetCut := cutEnv_of_subspt names source.locals locals env included cut
            have same : DataSem.evaluate (.call (some (returns, names)) dest arguments handler) { source with locals := locals } =
                DataSem.evaluate (.call (some (returns, names)) dest arguments handler) source := by
              simp [DataSem.evaluate, read, targetRead, found, unique, cut, targetCut, callEnv_push_changeLocals]
            simpa [compile, space, pMakeSpace] using
              simulationWitness_of_equal (.call (some (returns, names)) dest arguments handler) source sourceNext result locals (same.trans run)
        · simp [DataSem.evaluate, read, found, unique] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)

/-- Force uses identical thunk and callee states once its source variable
and optional saved environment have been read. -/
theorem simulationFor_force {C F : Type} (ret : Option (Nat × NumSet)) (label src : Nat) :
    simulationFor (C := C) (F := F) (.force ret label src) := by
  intro source sourceNext result locals notType run included
  cases read : DataSem.getVar src source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some thunk =>
    have targetRead : DataSem.getVar src locals = some thunk := (sptSubsptLookup _ _).1 included src thunk read
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
      | evaluated =>
        cases ret with
        | none =>
          have same : DataSem.evaluate (.force none label src) { source with locals := locals } =
              DataSem.evaluate (.force none label src) source := by
            simp [DataSem.evaluate, read, targetRead, inspect, flushState]
          simpa [compile, space, pMakeSpace] using
            simulationWitness_of_equal (.force none label src) source sourceNext result locals (same.trans run)
        | some pair =>
          obtain ⟨dest, names⟩ := pair
          cases cut : cutEnv names source.locals with
          | none =>
            simp [DataSem.evaluate, read, inspect, cut] at run
            obtain ⟨rfl, rfl⟩ := run
            exact False.elim (notType rfl)
          | some env =>
            have targetCut := cutEnv_of_subspt names source.locals locals env included cut
            have same : DataSem.evaluate (.force (some (dest, names)) label src) { source with locals := locals } =
                DataSem.evaluate (.force (some (dest, names)) label src) source := by
              simp [DataSem.evaluate, read, targetRead, inspect, cut, targetCut]
            simpa [compile, space, pMakeSpace] using
              simulationWitness_of_equal (.force (some (dest, names)) label src) source sourceNext result locals (same.trans run)
      | notEvaluated =>
        cases found : findCode (some label) [thunk, value] source.code source.stackFrameSizes with
        | none =>
          simp [DataSem.evaluate, read, inspect, found] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)
        | some triple =>
          obtain ⟨args, body, size⟩ := triple
          cases ret with
          | none =>
            have same : DataSem.evaluate (.force none label src) { source with locals := locals } =
                DataSem.evaluate (.force none label src) source := by
              by_cases zero : source.clock = 0
              · simp [DataSem.evaluate, read, targetRead, inspect, found, zero]
              · simp [DataSem.evaluate, read, targetRead, inspect, found, zero, callEnv_changeLocals]
            simpa [compile, space, pMakeSpace] using
              simulationWitness_of_equal (.force none label src) source sourceNext result locals (same.trans run)
          | some pair =>
            obtain ⟨dest, names⟩ := pair
            cases cut : cutEnv names source.locals with
            | none =>
              simp [DataSem.evaluate, read, inspect, found, cut] at run
              obtain ⟨rfl, rfl⟩ := run
              exact False.elim (notType rfl)
            | some env =>
              have targetCut := cutEnv_of_subspt names source.locals locals env included cut
              have same : DataSem.evaluate (.force (some (dest, names)) label src) { source with locals := locals } =
                  DataSem.evaluate (.force (some (dest, names)) label src) source := by
                simp [DataSem.evaluate, read, targetRead, inspect, found, cut, targetCut, callEnv_push_changeLocals]
              simpa [compile, space, pMakeSpace] using
                simulationWitness_of_equal (.force (some (dest, names)) label src) source sourceNext result locals (same.trans run)

/-- A conditional preserves the simulation when both branches do. -/
theorem simulationFor_if {C F : Type} (name : Nat) (yes no : DataLang.Prog)
    (yesIH : simulationFor (C := C) (F := F) yes)
    (noIH : simulationFor (C := C) (F := F) no) :
    simulationFor (C := C) (F := F) (.ifThenElse name yes no) := by
  intro source sourceNext result locals notType run included
  cases read : DataSem.getVar name source.locals with
  | none =>
    simp [DataSem.evaluate, read] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)
  | some value =>
    have targetRead : DataSem.getVar name locals = some value := (sptSubsptLookup _ _).1 included name value read
    by_cases isTrue : DataSem.isBool true value
    · have branch : DataSem.evaluate yes source = (result, sourceNext) := by
        simpa [DataSem.evaluate, read, isTrue] using run
      obtain ⟨out, safe, peak, stackMax, targetRun, final⟩ := yesIH source sourceNext result locals notType branch included
      refine ⟨out, safe, peak, stackMax, ?_, final⟩
      simpa [compile, space, pMakeSpace, DataSem.evaluate, targetRead, isTrue] using targetRun
    · by_cases isFalse : DataSem.isBool false value
      · have branch : DataSem.evaluate no source = (result, sourceNext) := by
          simpa [DataSem.evaluate, read, isTrue, isFalse] using run
        obtain ⟨out, safe, peak, stackMax, targetRun, final⟩ := noIH source sourceNext result locals notType branch included
        refine ⟨out, safe, peak, stackMax, ?_, final⟩
        simpa [compile, space, pMakeSpace, DataSem.evaluate, targetRead, isTrue, isFalse] using targetRun
      · simp [DataSem.evaluate, read, isTrue, isFalse] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)


end Flapjack.Compiler.Backend.DataSpace

import Flapjack.Compiler.Backend.DataSpace.Proofs.PrimitiveBlockSpace
import Flapjack.Compiler.Backend.DataSpace.Proofs.Simulation

/-! Reservation transport for unannotated assignments. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- A successful non-resetting space check changes only the reserved amount. -/
theorem doSpace_noNames_success {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state next : State C F)
    (valid : DataLang.opRequiresNames op = false) (run : doSpace op values state = some next) :
    next = { state with space := state.space - opSpaceReq op values.length } := by
  have noReset := noNames_noReset op valid
  by_cases zero : opSpaceReq op values.length = 0
  · simpa [doSpace, noReset, zero] using run.symm
  · by_cases enough : state.space < opSpaceReq op values.length
    · simp [doSpace, noReset, zero, consumeSpace, enough] at run
    · simpa [doSpace, noReset, zero, consumeSpace, enough] using run.symm

/-- On an unannotated operation, application first performs its space check
and then dispatches the primitive. -/
theorem doApp_noNames {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (valid : DataLang.opRequiresNames op = false) :
    doApp op values state =
      match doSpace op values state with
      | none => .err (.abort .typeError)
      | some next => doAppAux op values (doStack op values (doLimSafe next op values)) := by
  cases op with
  | install => simp [DataLang.opRequiresNames] at valid
  | ffi name => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at valid
  | intOp op => cases op <;> simp_all [doApp, DataLang.opRequiresNames, DataLang.opSpaceReset] <;> rfl
  | label label => rfl
  | wordOp op => rfl
  | blockOp op => rfl
  | globOp op => rfl
  | memOp op => rfl
  | thunkOp op => rfl

/-- If an unannotated primitive succeeds, supplying precisely its requirement
and extra reserved space gives the same value and state with that extra space. -/
theorem doApp_success_with_reservation {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state after : State C F) (value : DataSem.Value)
    (extra : Nat) (valid : DataLang.opRequiresNames op = false)
    (run : doApp op values state = .val (value, after)) :
    doApp op values { state with space := opSpaceReq op values.length + extra } =
      .val (value, { after with space := extra }) := by
  rw [doApp_noNames op values state valid] at run
  cases spaceRun : doSpace op values state with
  | none => simp [spaceRun] at run
  | some next =>
    have shape := doSpace_noNames_success op values state next valid spaceRun
    subst next
    simp only [spaceRun] at run
    rw [doApp_reserved_unannotated op values state extra valid]
    have stackEq : doStack op values (doLimSafe { state with space := extra } op values) =
        { doStack op values (doLimSafe { state with space := state.space - opSpaceReq op values.length } op values) with space := extra } := by
      rfl
    rw [stackEq, doAppAux_noNames_with_space op values _ extra valid, run]
    rfl

/-- An unannotated primitive cannot produce an FFI or other non-type error. -/
theorem doApp_noNames_error {C F : Type} (op : ClosLang.Op)
    (values : List DataSem.Value) (state : State C F) (error : ErrorResult DataSem.Value)
    (valid : DataLang.opRequiresNames op = false) (run : doApp op values state = .err error) :
    error = .abort .typeError := by
  rw [doApp_noNames op values state valid] at run
  cases found : doSpace op values state with
  | none => simpa [found] using run.symm
  | some next =>
    simp only [found] at run
    cases op with
    | ffi name => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at valid
    | install => simp [DataLang.opRequiresNames] at valid
    | label label | intOp label | wordOp label | blockOp label | globOp label | memOp label | thunkOp label =>
      simp only [doAppAux] at run
      split at run <;> simp_all

/-- Hoisting a reservation across an unannotated assignment preserves the
reservation simulation. This is Flapjack proof infrastructure. -/
theorem simulationFor_seq_assign_makeSpace {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (arguments : List Nat) (amount : Nat) (names : NumSet) :
    simulationFor (C := C) (F := F) (.seq (.assign dest op arguments none) (.makeSpace amount names)) := by
  intro source sourceNext result locals notType run included
  by_cases valid : DataLang.opRequiresNames op = false
  · cases read : DataSem.getVars arguments source.locals with
    | none =>
      simp [DataSem.evaluate, valid, read, fixClock] at run
      obtain ⟨rfl, rfl⟩ := run
      exact False.elim (notType rfl)
    | some values =>
      cases app : doApp op values source with
      | err error =>
        have errorEq := doApp_noNames_error op values source error valid app
        subst error
        simp [DataSem.evaluate, valid, read, cutStateOpt, app, fixClock] at run
        obtain ⟨rfl, rfl⟩ := run
        exact False.elim (notType rfl)
      | val pair =>
        obtain ⟨value, applied⟩ := pair
        have control := doApp_control op values source applied value app
        let assigned := setVar dest value (installSfs op applied)
        have assignRun : DataSem.evaluate (.assign dest op arguments none) source = (none, assigned) := by
          simp [DataSem.evaluate, valid, read, cutStateOpt, app, assigned]
        rw [DataSem.evaluate, fixClock_evaluate, assignRun] at run
        cases cut : cutEnv names assigned.locals with
        | none =>
          simp [DataSem.evaluate, cut] at run
          obtain ⟨rfl, rfl⟩ := run
          exact False.elim (notType rfl)
        | some resultEnv =>
          have sourceCut : cutEnv names (sptInsert dest value source.locals) = some resultEnv := by
            simpa [assigned, setVar, installSfs, control.1] using cut
          obtain ⟨before, beforeCut, beforeRead, afterIncluded⟩ :=
            cutEnv_before_assign source.locals locals names dest arguments values value resultEnv included read sourceCut
          simp [DataSem.evaluate, cut] at run
          obtain ⟨rfl, rfl⟩ := run
          let requirement := opSpaceReq op values.length
          let reserved := { source with space := requirement + amount }
          let targetMid := addSpace { source with locals := before } (requirement + amount)
          have reservedApp : doApp op values reserved = .val (value, { applied with space := amount }) := by
            exact doApp_success_with_reservation op values source applied value amount valid app
          have related : DataLive.stateRel reserved targetMid .ln := by
            simp [DataLive.stateRel, reserved, targetMid, addSpace, sptMem, sptDomain, sptLookup]
          obtain ⟨targetApplied, targetApp, appRel⟩ :=
            DataLive.stateRel_doApp_success reserved targetMid { applied with space := amount } .ln op values value related reservedApp
          have targetControl := doApp_control op values targetMid targetApplied value targetApp
          have stateEq : targetApplied = { applied with locals := before, space := amount, safeForSpace := targetApplied.safeForSpace, peakHeapLength := targetApplied.peakHeapLength, stackMax := targetApplied.stackMax } := by
            rcases appRel with ⟨code, clock, spaceEq, ffi, refs, global, handler, _, compiler, oracle, stamps, limits, frames, _⟩
            cases applied
            cases targetApplied
            simp_all [targetMid, addSpace]
          let targetNext := setVar dest value (installSfs op targetApplied)
          refine ⟨sptInsert dest value before, targetNext.safeForSpace, targetNext.peakHeapLength,
            targetNext.stackMax, ?_, ?_⟩
          · change DataSem.evaluate (.seq (.makeSpace (opSpaceReq op arguments.length + amount)
                (sptListInsert arguments (sptDelete dest names))) (.seq (.assign dest op arguments none) .skip))
                { source with locals := locals } = _
            have reqEq := read_requirement arguments source.locals values op read
            have reserveRun : DataSem.evaluate (.makeSpace (opSpaceReq op arguments.length + amount)
                (sptListInsert arguments (sptDelete dest names))) { source with locals := locals } = (none, targetMid) := by
              simp [DataSem.evaluate, beforeCut, targetMid, requirement, reqEq]
            rw [DataSem.evaluate, fixClock_evaluate, reserveRun, DataSem.evaluate_seq_skip]
            have targetRead : DataSem.getVars arguments targetMid.locals = some values := by
              simpa [targetMid, addSpace] using beforeRead
            have targetRun : DataSem.evaluate (.assign dest op arguments none) targetMid = (none, targetNext) := by
              simp [DataSem.evaluate, valid, targetRead, cutStateOpt, targetApp, targetNext]
            rw [targetRun]
            dsimp only [targetNext]
            rw [stateEq]
            simp [assigned, setVar, installSfs, addSpace]
          · simpa [assigned, setVar, installSfs, addSpace, control.1] using afterIncluded
  · have invalid : DataLang.opRequiresNames op = true := by cases h : DataLang.opRequiresNames op <;> simp_all
    simp [DataSem.evaluate, invalid, fixClock] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)

end Flapjack.Compiler.Backend.DataSpace

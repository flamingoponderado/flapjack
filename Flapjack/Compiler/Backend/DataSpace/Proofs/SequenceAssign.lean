import Flapjack.Compiler.Backend.DataSpace.Proofs.SequenceMove
import Flapjack.Compiler.Backend.DataSpace.Proofs.ReservationAssign

/-! Hoisting deferred reservations across primitive assignments. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- An unannotated assignment followed by an arbitrary component with a
deferred reservation preserves the data-space simulation. -/
theorem simulationFor_seq_assign_deferred {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (arguments : List Nat) (second : DataLang.Prog) (amount : Nat) (names : NumSet) (body : DataLang.Prog)
    (found : space second = .inr (amount, names, body))
    (secondIH : simulationFor (C := C) (F := F) second) :
    simulationFor (C := C) (F := F) (.seq (.assign dest op arguments none) second) := by
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
        have reflexive : sptSubspt assigned.locals assigned.locals := by
          intro key member
          exact ⟨member, rfl⟩
        obtain ⟨out, safe, peak, stackMax, secondRun, finalIncluded⟩ :=
          secondIH assigned sourceNext result assigned.locals notType run reflexive
        have secondRun' : DataSem.evaluate (.seq (.makeSpace amount names) body) assigned =
            (result, if result = none then { sourceNext with locals := out, safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }
              else { sourceNext with safeForSpace := safe, peakHeapLength := peak, stackMax := stackMax }) := by
          simpa [compile, found, pMakeSpace] using secondRun
        cases cut : cutEnv names assigned.locals with
        | none =>
          simp [DataSem.evaluate, cut, fixClock] at secondRun'
          obtain ⟨rfl, _⟩ := secondRun'
          exact False.elim (notType rfl)
        | some finalEnv =>
          have sourceCut : cutEnv names (sptInsert dest value source.locals) = some finalEnv := by
            simpa [assigned, setVar, installSfs, control.1] using cut
          obtain ⟨before, beforeCut, beforeRead, afterIncluded⟩ :=
            cutEnv_before_assign source.locals locals names dest arguments values value finalEnv included read sourceCut
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
          let bodyStart := addSpace { assigned with locals := finalEnv } amount
          have reserveRun : DataSem.evaluate (.makeSpace amount names) assigned = (none, bodyStart) := by
            simp [DataSem.evaluate, cut, bodyStart]
          rw [DataSem.evaluate, fixClock_evaluate, reserveRun] at secondRun'
          have bodyIncluded : sptSubspt bodyStart.locals (sptInsert dest value before) := by
            simpa [bodyStart, addSpace] using afterIncluded
          obtain ⟨out', safe', peak', max', extendedRun, finalExtended⟩ :=
            evaluate_locals_extension body bodyStart _ result (sptInsert dest value before) notType secondRun' bodyIncluded
          let targetStart := setVar dest value (installSfs op targetApplied)
          let extendedStart := { bodyStart with locals := sptInsert dest value before }
          have targetShape : targetStart = { extendedStart with safeForSpace := targetStart.safeForSpace, peakHeapLength := targetStart.peakHeapLength, stackMax := targetStart.stackMax } := by
            dsimp only [targetStart]
            rw [stateEq]
            simp [extendedStart, bodyStart, assigned, setVar, installSfs, addSpace]
          obtain ⟨safe'', peak'', max'', varied⟩ := evaluate_resource_variation_exact body extendedStart _ result
            targetStart.safeForSpace targetStart.peakHeapLength targetStart.stackMax notType extendedRun
          rw [← targetShape] at varied
          refine ⟨out', safe'', peak'', max'', ?_, ?_⟩
          · simp only [compile, space, found, pMakeSpace]
            have reqEq := read_requirement arguments source.locals values op read
            have targetReserve : DataSem.evaluate (.makeSpace (opSpaceReq op arguments.length + amount)
                (sptListInsert arguments (sptDelete dest names))) { source with locals := locals } = (none, targetMid) := by
              simp [DataSem.evaluate, beforeCut, targetMid, requirement, reqEq]
            have targetRead : DataSem.getVars arguments targetMid.locals = some values := by
              simpa [targetMid, addSpace] using beforeRead
            have targetAssign : DataSem.evaluate (.assign dest op arguments none) targetMid = (none, targetStart) := by
              simp [DataSem.evaluate, valid, targetRead, cutStateOpt, targetApp, targetStart]
            rw [DataSem.evaluate, fixClock_evaluate, targetReserve, DataSem.evaluate, fixClock_evaluate, targetAssign]
            cases result <;> simpa using varied
          · cases result with
            | none => exact sptSubsptTrans _ _ _ ⟨finalIncluded, by simpa using finalExtended⟩
            | some stopped => simpa using finalExtended
  · have invalid : DataLang.opRequiresNames op = true := by cases h : DataLang.opRequiresNames op <;> simp_all
    simp [DataSem.evaluate, invalid, fixClock] at run
    obtain ⟨rfl, rfl⟩ := run
    exact False.elim (notType rfl)

/-- An unannotated assignment composes with any simulated second component. -/
theorem simulationFor_seq_assign_left {C F : Type} (dest : Nat) (op : ClosLang.Op)
    (arguments : List Nat) (second : DataLang.Prog) (secondIH : simulationFor (C := C) (F := F) second) :
    simulationFor (C := C) (F := F) (.seq (.assign dest op arguments none) second) := by
  cases found : space second with
  | inl body =>
    apply simulationFor_seq_withoutDeferred (.assign dest op arguments none) second body
      (simulationFor_assign dest op arguments none) secondIH found
    · simp
    · intros; simp
  | inr payload =>
    obtain ⟨amount, names, body⟩ := payload
    exact simulationFor_seq_assign_deferred dest op arguments second amount names body found secondIH

end Flapjack.Compiler.Backend.DataSpace

module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveInstall

@[expose] public section

/-! Thunk primitive simulation for the liveness pass. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- The thunk auxiliary dispatcher produces matching results and related
reference stores. This theorem is untagged pending source evaluator review. -/
theorem stateRel_doAppAux_thunk {C F : Type} (source target : State C F) (live : NumSet)
    (op : AstHOL.ThunkOp) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.thunkOp op) args source) (doAppAux (.thunkOp op) args target) := by
  have refs := related.2.2.2.2.1
  cases op with
  | forceThunk => cases args <;> simp [doAppAux, applyNonFfi, appRel]
  | allocThunk mode =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        by_cases bad : badThunkUpdate mode first source.refs
        · simp [doAppAux, applyNonFfi, appRel, ← refs, bad]
        · simpa [doAppAux, applyNonFfi, appRel, ← refs, bad] using
            stateRel_setRefs source target live
              (sptInsert (leastUnusedRef source.refs) (.thunk mode first) source.refs) related
  | updateThunk mode =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, appRel]
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi, appRel]
        | nil =>
          cases first <;> simp [doAppAux, applyNonFfi, appRel]
          case refPtr flag ptr =>
            cases flag with
            | true => simp
            | false =>
              by_cases bad : badThunkUpdate mode second source.refs
              · simp [← refs, bad]
              · cases found : sptLookup ptr source.refs with
                | none => simp [← refs, bad, found]
                | some entry =>
                  cases entry <;> simp [← refs, bad, found]
                  case thunk oldMode oldValue =>
                    cases oldMode <;> simp
                    simpa [← refs, appRel] using
                      stateRel_setRefs source target live (sptInsert ptr (.thunk mode second) source.refs) related

/-- The full thunk dispatcher preserves related primitive outcomes. -/
theorem stateRel_doApp_thunk {C F : Type} (source target : State C F) (live : NumSet)
    (op : AstHOL.ThunkOp) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doApp (.thunkOp op) args source) (doApp (.thunkOp op) args target) := by
  simp only [doApp]
  rcases stateRel_doSpace source target live (.thunkOp op) args related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
  · simp [failed.1, failed.2, appRel]
  · simp only [sourceRun, targetRun]
    exact stateRel_doAppAux_thunk _ _ live op args (stateRel_doStackLim sourceNext targetNext live (.thunkOp op) args nextRel)

/-- Thunk assignments satisfy the liveness simulation with or without a
live-name annotation. -/
theorem simulationFor_assign_thunk_all {C F : Type} (dest : Nat) (op : AstHOL.ThunkOp)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.thunkOp op) args names) live := by
  cases names with
  | none =>
    apply simulationFor_retained_of_appRel dest (.thunkOp op) args live (by simp [isPure])
    intro source target values related
    exact stateRel_doApp_thunk source target _ op values related
  | some names =>
    apply simulationFor_annotated_of_appRel dest (.thunkOp op) args names live
    intro source target values related
    exact stateRel_doApp_thunk source target _ op values related

end Flapjack.Compiler.Backend.DataLive

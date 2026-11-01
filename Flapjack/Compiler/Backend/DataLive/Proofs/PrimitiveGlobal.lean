import Flapjack.Compiler.Backend.DataLive.Proofs.Accounting

/-! Global primitive simulation for the liveness pass. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Updating related states with the same reference store preserves the
liveness relation. This is auxiliary proof infrastructure. -/
theorem stateRel_setRefs {C F : Type} (source target : State C F) (live : NumSet)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (related : stateRel source target live) :
    stateRel { source with refs := refs } { target with refs := refs } live := by
  rcases related with ⟨code, clock, space, ffi, _, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  exact ⟨code, clock, space, ffi, rfl, global, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩

/-- Updating related states with the same global pointer preserves the
liveness relation. -/
theorem stateRel_setGlobal {C F : Type} (source target : State C F) (live : NumSet)
    (global : Option Nat) (related : stateRel source target live) :
    stateRel { source with global := global } { target with global := global } live := by
  rcases related with ⟨code, clock, space, ffi, refs, _, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩
  exact ⟨code, clock, space, ffi, refs, rfl, handler, stack, compiler, oracle, stamps, limits, frames, locals⟩

/-- The global auxiliary dispatcher produces matching errors or values and
related result states. This is untagged pending source evaluator review. -/
theorem stateRel_doAppAux_global {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.GlobOp) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.globOp op) args source) (doAppAux (.globOp op) args target) := by
  have globals := related.2.2.2.2.2.1
  have refs := related.2.2.2.2.1
  cases op with
  | allocGlobal => simp [doAppAux, applyNonFfi, appRel]
  | globalsPtr =>
    cases args with
    | cons first rest => simp [doAppAux, applyNonFfi, appRel]
    | nil =>
      cases found : source.global with
      | none => simp [doAppAux, applyNonFfi, appRel, found, ← globals]
      | some ptr => simpa [doAppAux, applyNonFfi, appRel, found, ← globals] using related
  | setGlobalsPtr =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases first <;> simp [doAppAux, applyNonFfi, appRel]
        case refPtr flag ptr =>
          cases flag <;> simp
          exact stateRel_setGlobal source target live (some ptr) related
  | global index =>
    cases args with
    | cons first rest => simp [doAppAux, applyNonFfi, appRel]
    | nil =>
      cases foundGlobal : source.global with
      | none => simp [doAppAux, applyNonFfi, appRel, foundGlobal, ← globals]
      | some ptr =>
        cases found : sptLookup ptr source.refs with
        | none => simp [doAppAux, applyNonFfi, appRel, foundGlobal, ← globals, found, ← refs]
        | some entry =>
          cases entry <;> simp [doAppAux, applyNonFfi, appRel, foundGlobal, ← globals, found, ← refs]
          case valueArray values =>
            cases slot : values[index]? with
            | none => simp
            | some value => simpa [slot, appRel] using related
  | setGlobal index =>
    cases args with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases foundGlobal : source.global with
        | none => simp [doAppAux, applyNonFfi, appRel, foundGlobal, ← globals]
        | some ptr =>
          cases found : sptLookup ptr source.refs with
          | none => simp [doAppAux, applyNonFfi, appRel, foundGlobal, ← globals, found, ← refs]
          | some entry =>
            cases entry <;> simp [doAppAux, applyNonFfi, appRel, foundGlobal, ← globals, found, ← refs]
            case valueArray values =>
              by_cases bound : index < values.length
              · simpa [bound, foundGlobal, ← globals, appRel] using stateRel_setRefs source target live
                  (sptInsert ptr (.valueArray (values.set index first)) source.refs) related
              · simp [bound]

/-- The full global dispatcher produces matching outcomes and related
states, including space-accounting and mutating global operations. -/
theorem stateRel_doApp_global {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.GlobOp) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doApp (.globOp op) args source) (doApp (.globOp op) args target) := by
  simp only [doApp]
  rcases stateRel_doSpace source target live (.globOp op) args related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
  · simp [failed.1, failed.2, appRel]
  · simp only [sourceRun, targetRun]
    exact stateRel_doAppAux_global _ _ live op args (stateRel_doStackLim sourceNext targetNext live (.globOp op) args nextRel)

/-- Every unannotated global assignment satisfies the liveness simulation. -/
theorem simulationFor_assign_global {C F : Type} (dest : Nat) (op : ClosLang.GlobOp)
    (args : List Nat) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.globOp op) args none) live := by
  cases retained : ((sptLookup dest live).isNone && isPure (.globOp op)) with
  | false =>
    apply simulationFor_retained_of_appRel dest (.globOp op) args live retained
    intro source target values related
    exact stateRel_doApp_global source target _ op values related
  | true =>
    have parts : (sptLookup dest live).isNone = true ∧ isPure (.globOp op) = true := by simpa using retained
    have dead : sptLookup dest live = none := Option.isNone_iff_eq_none.mp parts.1
    exact simulationFor_removed_global dest op args live parts.2 dead

/-- Every global assignment satisfies the liveness simulation with or
without a live-name annotation. -/
theorem simulationFor_assign_global_all {C F : Type} (dest : Nat) (op : ClosLang.GlobOp)
    (args : List Nat) (names : Option NumSet) (live : NumSet) :
    simulationFor (C := C) (F := F) (.assign dest (.globOp op) args names) live := by
  cases names with
  | none => exact simulationFor_assign_global dest op args live
  | some names =>
    apply simulationFor_annotated_of_appRel dest (.globOp op) args names live
    intro source target values related
    exact stateRel_doApp_global source target _ op values related

end Flapjack.Compiler.Backend.DataLive

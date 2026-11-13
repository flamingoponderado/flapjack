module

public import Flapjack.Compiler.Backend.DataLive.Proofs.PrimitiveBlockAlloc

@[expose] public section

/-! Allocation primitive simulation for the liveness pass. -/
namespace Flapjack.Compiler.Backend.DataLive
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Related states allocate the same fresh reference and store. This is
untagged pending source evaluator and state-carrier review. -/
theorem stateRel_doAppAux_ref {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .ref) args source) (doAppAux (.memOp .ref) args target) := by
  have refs := related.2.2.2.2.1
  simpa [doAppAux, applyNonFfi, appRel, ← refs] using
    stateRel_setRefs source target live
      (sptInsert (leastUnusedRef source.refs) (.valueArray args) source.refs) related

/-- Related states allocate equal value arrays. -/
theorem stateRel_doAppAux_refArray {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .refArray) args source) (doAppAux (.memOp .refArray) args target) := by
  have refs := related.2.2.2.2.1
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
        case number count =>
          by_cases negative : count < 0
          · simp [negative]
          · simpa [negative, ← refs, appRel] using stateRel_setRefs source target live
              (sptInsert (leastUnusedRef source.refs) (.valueArray (List.replicate count.toNat second)) source.refs) related

/-- Related states allocate equal byte arrays. -/
theorem stateRel_doAppAux_refByte {C F : Type} (source target : State C F) (live : NumSet)
    (flag : Bool) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp (.refByte flag)) args source) (doAppAux (.memOp (.refByte flag)) args target) := by
  have refs := related.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | nil => simp [doAppAux, applyNonFfi, appRel]
    | cons second tail =>
      cases tail with
      | cons third tail => simp [doAppAux, applyNonFfi, appRel]
      | nil =>
        cases first <;> cases second <;> simp [doAppAux, applyNonFfi, appRel]
        case number.number count byte =>
          by_cases negative : count < 0
          · simp [negative]
          · cases converted : ClosSem.intToByte byte with
            | none => simp [negative]
            | some b =>
              simpa [negative, converted, ← refs, appRel] using stateRel_setRefs source target live
                (sptInsert (leastUnusedRef source.refs) (.byteArray flag (List.replicate count.toNat b)) source.refs) related

/-- Lifting any memory auxiliary relation through resource accounting. -/
theorem stateRel_doApp_memory_of_aux {C F : Type} (source target : State C F) (live : NumSet)
    (op : ClosLang.MemOp) (args : List DataSem.Value) (related : stateRel source target live)
    (aux : ∀ left right : State C F, stateRel left right live →
      appRel live (doAppAux (.memOp op) args left) (doAppAux (.memOp op) args right)) :
    appRel live (doApp (.memOp op) args source) (doApp (.memOp op) args target) := by
  simp only [doApp]
  rcases stateRel_doSpace source target live (.memOp op) args related with failed | ⟨sourceNext, targetNext, sourceRun, targetRun, nextRel⟩
  · simp [failed.1, failed.2, appRel]
  · simp only [sourceRun, targetRun]
    exact aux _ _ (stateRel_doStackLim sourceNext targetNext live (.memOp op) args nextRel)

/-- A memory operation with a related primitive dispatcher satisfies the
liveness assignment simulation. -/
theorem simulationFor_assign_memory_of_aux {C F : Type} (dest : Nat) (op : ClosLang.MemOp)
    (args : List Nat) (names : Option NumSet) (live : NumSet)
    (aux : ∀ (source target : State C F) (values : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doAppAux (.memOp op) values source) (doAppAux (.memOp op) values target)) :
    simulationFor (C := C) (F := F) (.assign dest (.memOp op) args names) live := by
  have primitiveRel : ∀ (source target : State C F) (values : List DataSem.Value),
      stateRel source target (sptDelete dest live) →
      appRel (sptDelete dest live) (doApp (.memOp op) values source) (doApp (.memOp op) values target) := by
    intro source target values related
    apply stateRel_doApp_memory_of_aux source target _ op values related
    intro left right relation
    exact aux left right values relation
  cases names with
  | none =>
    cases retained : ((sptLookup dest live).isNone && isPure (.memOp op)) with
    | false => exact simulationFor_retained_of_appRel dest (.memOp op) args live retained primitiveRel
    | true =>
      have parts : (sptLookup dest live).isNone = true ∧ isPure (.memOp op) = true := by simpa using retained
      exact simulationFor_removed_memory dest op args live parts.2 (Option.isNone_iff_eq_none.mp parts.1)
  | some names => exact simulationFor_annotated_of_appRel dest (.memOp op) args names live primitiveRel

/-- Related states allocate the same mutable constructor. -/
theorem stateRel_doAppAux_mutCons {C F : Type} (source target : State C F) (live : NumSet)
    (tag index : Nat) (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp (.mutCons tag index)) args source)
      (doAppAux (.memOp (.mutCons tag index)) args target) := by
  have refs := related.2.2.2.2.1
  cases found : args[index]? with
  | none => simp [doAppAux, applyNonFfi, appRel, found]
  | some child =>
    simpa [doAppAux, applyNonFfi, appRel, found, ← refs] using stateRel_setRefs source target live
      (sptInsert (leastUnusedRef source.refs) (.mutBlock tag false (args.take index) child (args.drop (index + 1))) source.refs) related

/-- Setting the same reference store and timestamp preserves the relation. -/
theorem stateRel_setRefsStamps {C F : Type} (source target : State C F) (live : NumSet)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (stamps : Option Nat) (related : stateRel source target live) :
    stateRel { source with refs := refs, tstamps := stamps } { target with refs := refs, tstamps := stamps } live := by
  rcases related with ⟨code, clock, space, ffi, _, global, handler, stack, compiler, oracle, _, limits, frames, locals⟩
  exact ⟨code, clock, space, ffi, rfl, global, handler, stack, compiler, oracle, rfl, limits, frames, locals⟩

/-- Related states finalise a constructor to the same value and store. -/
theorem stateRel_doAppAux_finaliseCons {C F : Type} (source target : State C F) (live : NumSet)
    (args : List DataSem.Value) (related : stateRel source target live) :
    appRel live (doAppAux (.memOp .finaliseCons) args source)
      (doAppAux (.memOp .finaliseCons) args target) := by
  have refs := related.2.2.2.2.1
  have stamps := related.2.2.2.2.2.2.2.2.2.2.1
  cases args with
  | nil => simp [doAppAux, applyNonFfi, appRel]
  | cons first rest =>
    cases rest with
    | cons second tail => simp [doAppAux, applyNonFfi, appRel]
    | nil =>
      cases finalised : finaliseCons first source.refs source.tstamps with
      | none => simp [doAppAux, applyNonFfi, appRel, ← refs, ← stamps, finalised]
      | some triple =>
        obtain ⟨value, nextRefs, nextStamps⟩ := triple
        simpa [doAppAux, applyNonFfi, appRel, ← refs, ← stamps, finalised] using
          stateRel_setRefsStamps source target live nextRefs nextStamps related

end Flapjack.Compiler.Backend.DataLive

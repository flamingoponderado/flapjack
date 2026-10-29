import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.Thunk
import Flapjack.Compiler.Backend.Semantics.ClosSem.Thunk

/-! Thunk inspection across the preliminary flat-to-closure relation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- Correspondence of thunk inspection results. -/
inductive ThunkResultRel : FlatSem.DestThunkResult → ClosSem.DestThunkResult → Prop where
  | badRef : ThunkResultRel .badRef .badRef
  | notThunk : ThunkResultRel .notThunk .notThunk
  | isThunk {mode source target} (related : ValueRel source target) :
      ThunkResultRel (.isThunk mode source) (.isThunk mode target)

/-- Inspecting related singleton values in related stores yields related
thunk outcomes, including invalid references and non-thunk arrays. -/
theorem destThunk_related (source : FlatSem.Value) (target : ClosSem.Value)
    (refs : Store FlatSem.Value) (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (values : ValueRel source target) (stores : StoreRel refs targetRefs) :
    ThunkResultRel (FlatSem.destThunk [source] refs) (ClosSem.destThunk [target] targetRefs) := by
  cases values with
  | loc flag index =>
    have store := stores index
    cases found : storeLookup index refs with
    | none =>
      change refs[index]? = none at found
      simp only [found] at store
      simp [FlatSem.destThunk, storeLookup, found, ClosSem.destThunk, store, ThunkResultRel.badRef]
    | some entry =>
      change refs[index]? = some entry at found
      cases entry with
      | refv value =>
        simp only [found] at store
        obtain ⟨targetValue, targetFound, _⟩ := store
        simp [FlatSem.destThunk, storeLookup, found, ClosSem.destThunk, targetFound, ThunkResultRel.notThunk]
      | w8array bytes =>
        simp only [found] at store
        simp [FlatSem.destThunk, storeLookup, found, ClosSem.destThunk, store, ThunkResultRel.notThunk]
      | varray values =>
        simp only [found] at store
        obtain ⟨targetValues, targetFound, _⟩ := store
        simp [FlatSem.destThunk, storeLookup, found, ClosSem.destThunk, targetFound, ThunkResultRel.notThunk]
      | thunk mode value =>
        simp only [found] at store
        obtain ⟨targetValue, targetFound, valueRel⟩ := store
        cases flag <;> simp [FlatSem.destThunk, storeLookup, found, ClosSem.destThunk, targetFound,
          ThunkResultRel.badRef, ThunkResultRel.isThunk valueRel]
  | int | char | string | word8 | word64 | float64 | tuple | con | vector | closure | recclosure =>
    exact .notThunk

/-- Thunk inspection also agrees for arbitrary related argument lists. -/
theorem destThunk_list_related (source : List FlatSem.Value) (target : List ClosSem.Value)
    (refs : Store FlatSem.Value) (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (values : List.Forall₂ ValueRel source target) (stores : StoreRel refs targetRefs) :
    ThunkResultRel (FlatSem.destThunk source refs) (ClosSem.destThunk target targetRefs) := by
  cases values with
  | nil => exact .notThunk
  | cons first rest =>
    cases rest with
    | nil => exact destThunk_related _ _ refs targetRefs first stores
    | cons _ _ => simpa [FlatSem.destThunk, ClosSem.destThunk] using ThunkResultRel.notThunk

/-- Related values agree on whether an evaluated thunk update is invalid. -/
theorem badThunkUpdate_related (mode : Flapjack.AstHOL.ThunkMode)
    (source : FlatSem.Value) (target : ClosSem.Value)
    (refs : Store FlatSem.Value) (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (values : ValueRel source target) (stores : StoreRel refs targetRefs) :
    FlatSem.badThunkUpdate mode source refs = ClosSem.badThunkUpdate mode target targetRefs := by
  have related := destThunk_related source target refs targetRefs values stores
  unfold FlatSem.badThunkUpdate ClosSem.badThunkUpdate
  generalize FlatSem.destThunk [source] refs = first at related ⊢
  generalize ClosSem.destThunk [target] targetRefs = second at related ⊢
  cases mode <;> cases related <;> rfl

/-- Replacing an existing source slot and its corresponding closure slot by
related thunk payloads preserves the store relation. -/
theorem storeRel_setThunk (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (index : Nat) (old : StoreValue FlatSem.Value) (mode : Flapjack.AstHOL.ThunkMode)
    (source : FlatSem.Value) (target : ClosSem.Value)
    (stores : StoreRel refs targetRefs) (found : refs[index]? = some old)
    (values : ValueRel source target) :
    StoreRel (refs.set index (.thunk mode source)) (targetRefs.updateEq (index, .thunk mode target)) := by
  have bound : index < refs.length := (List.getElem?_eq_some_iff.mp found).choose
  intro key
  by_cases same : index = key
  · subst key
    simp [bound, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, values]
  · have previous := stores key
    simpa [List.getElem?_set, same, Ne.symm same, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL] using previous

/-- Updating a related unevaluated thunk with related non-thunk contents
produces related stores on both sides. -/
theorem updateThunk_related (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) (index : Nat)
    (old source : FlatSem.Value) (target : ClosSem.Value)
    (stores : StoreRel refs targetRefs) (values : ValueRel source target)
    (found : refs[index]? = some (.thunk .notEvaluated old))
    (safe : FlatSem.destThunk [source] refs = .notThunk) :
    FlatSem.updateThunk [.loc false index] refs [source] =
        some (refs.set index (.thunk .evaluated source)) ∧
    ClosSem.updateThunk [.refPtr false index] targetRefs [target] =
        some (targetRefs.updateEq (index, .thunk .evaluated target)) ∧
    StoreRel (refs.set index (.thunk .evaluated source))
      (targetRefs.updateEq (index, .thunk .evaluated target)) := by
  have slot := stores index
  simp only [found] at slot
  obtain ⟨oldTarget, targetFound, _⟩ := slot
  have targetSafe : ClosSem.destThunk [target] targetRefs = .notThunk := by
    have h := destThunk_related source target refs targetRefs values stores
    rw [safe] at h
    generalize ClosSem.destThunk [target] targetRefs = outcome at h ⊢
    cases h
    rfl
  refine ⟨?_, ?_, storeRel_setThunk refs targetRefs index _ .evaluated source target stores found values⟩
  · simp [FlatSem.updateThunk, safe, storeAssign, found, storeValueSameType]
  · simp [ClosSem.updateThunk, targetSafe, ClosSem.storeThunk, targetFound]

/-- Invert a successful flat thunk update: the target is a writable thunk,
and the replacement is a single non-thunk value. -/
theorem updateThunk_success_parts (targets : List FlatSem.Value) (refs updated : Store FlatSem.Value)
    (values : List FlatSem.Value) (run : FlatSem.updateThunk targets refs values = some updated) :
    ∃ index old value, targets = [.loc false index] ∧ values = [value] ∧
      refs[index]? = some (.thunk .notEvaluated old) ∧
      FlatSem.destThunk [value] refs = .notThunk ∧
      updated = refs.set index (.thunk .evaluated value) := by
  cases targets with
  | nil => simp [FlatSem.updateThunk] at run
  | cons target rest =>
    cases rest with
    | cons first rest => simp [FlatSem.updateThunk] at run
    | nil =>
      cases values with
      | nil => simp [FlatSem.updateThunk] at run
      | cons value rest =>
        cases rest with
        | cons first rest => simp [FlatSem.updateThunk] at run
        | nil =>
          cases target <;> simp [FlatSem.updateThunk] at run
          case loc flag index =>
            cases flag with
            | true => simp at run
            | false =>
              cases safe : FlatSem.destThunk [value] refs with
              | badRef | isThunk => simp [safe] at run
              | notThunk =>
                cases found : refs[index]? with
                | none => simp [safe, storeAssign, found] at run
                | some old =>
                  cases old with
                  | refv | w8array | varray => simp [safe, storeAssign, found, storeValueSameType] at run
                  | thunk mode old =>
                    cases mode with
                    | evaluated => simp [safe, storeAssign, found, storeValueSameType] at run
                    | notEvaluated =>
                      simp [safe, storeAssign, found, storeValueSameType] at run
                      exact ⟨index, old, value, rfl, rfl, found, safe, run.symm⟩

/-- Any successful flat thunk update has a corresponding successful closure
update, preserving the store relation. -/
theorem updateThunk_success_related (targets : List FlatSem.Value) (targetTargets : List ClosSem.Value)
    (refs updated : Store FlatSem.Value) (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value))
    (values : List FlatSem.Value) (targetValues : List ClosSem.Value)
    (targetsRel : List.Forall₂ ValueRel targets targetTargets)
    (valuesRel : List.Forall₂ ValueRel values targetValues) (stores : StoreRel refs targetRefs)
    (run : FlatSem.updateThunk targets refs values = some updated) :
    ∃ targetUpdated, ClosSem.updateThunk targetTargets targetRefs targetValues = some targetUpdated ∧
      StoreRel updated targetUpdated := by
  obtain ⟨index, old, value, rfl, rfl, found, safe, rfl⟩ := updateThunk_success_parts targets refs updated values run
  cases targetsRel with
  | cons targetRel targetTail =>
    cases targetTail
    cases targetRel with
    | loc =>
      cases valuesRel with
      | cons valueRel valueTail =>
        cases valueTail
        obtain ⟨_, targetRun, related⟩ := updateThunk_related refs targetRefs index old value _ stores valueRel found safe
        exact ⟨_, targetRun, related⟩

/-- A successful flat thunk update can be mirrored in the closure state. -/
theorem stateRel_updateThunk {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (sourceTargets : List FlatSem.Value) (targetTargets : List ClosSem.Value)
    (sourceValues : List FlatSem.Value) (targetValues : List ClosSem.Value) (updated : Store FlatSem.Value)
    (states : StateRel source target) (targetsRel : List.Forall₂ ValueRel sourceTargets targetTargets)
    (valuesRel : List.Forall₂ ValueRel sourceValues targetValues)
    (run : FlatSem.updateThunk sourceTargets source.refs sourceValues = some updated) :
    ∃ targetUpdated, ClosSem.updateThunk targetTargets target.refs targetValues = some targetUpdated ∧
      StateRel { source with refs := updated } { target with refs := targetUpdated } := by
  obtain ⟨targetUpdated, targetRun, stores⟩ :=
    updateThunk_success_related sourceTargets targetTargets source.refs updated target.refs sourceValues targetValues
      targetsRel valuesRel states.2.2.2.1 run
  rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
  exact ⟨targetUpdated, targetRun, maxApp, ffi, clock, stores, globals, values, install⟩

end Flapjack.Compiler.Backend.FlatToClos

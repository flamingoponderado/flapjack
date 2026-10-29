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

end Flapjack.Compiler.Backend.FlatToClos

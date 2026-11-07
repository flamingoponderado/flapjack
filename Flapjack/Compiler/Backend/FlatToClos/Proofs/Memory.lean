import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.ClosSem.ApplyMemory
import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyMemory

/-! Memory-store prerequisites for flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL

/-- Every source store index below the list length is present in a related
closure store. -/
theorem storeRel_occupied (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) (index : Nat)
    (stores : StoreRel refs targetRefs) (bound : index < refs.length) :
    targetRefs.lookup index ≠ none := by
  have slot := stores index
  have found : refs[index]? = some refs[index] := List.getElem?_eq_some_iff.mpr ⟨bound, rfl⟩
  rw [found] at slot
  cases entry : refs[index] <;> simp only [entry] at slot
  case refv value => obtain ⟨_, h, _⟩ := slot; simp [h]
  case w8array bytes => simp [slot]
  case varray values => obtain ⟨_, h, _⟩ := slot; simp [h]
  case thunk mode value => obtain ⟨_, h, _⟩ := slot; simp [h]

/-- The least unused target reference is the next source list index. -/
theorem leastUnusedRef_eq_length (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) (stores : StoreRel refs targetRefs) :
    ClosSem.leastUnusedRef targetRefs = refs.length := by
  have free : targetRefs.lookup refs.length = none := by
    have slot := stores refs.length
    simpa using slot
  have smaller : ClosSem.leastUnusedRef targetRefs ≤ refs.length := by
    by_contra h
    have used := ClosSem.leastUnusedRef_minimal targetRefs refs.length (by omega)
    exact used free
  have larger : refs.length ≤ ClosSem.leastUnusedRef targetRefs := by
    by_contra h
    have used := storeRel_occupied refs targetRefs (ClosSem.leastUnusedRef targetRefs) stores (by omega)
    exact used (ClosSem.leastUnusedRef_unused targetRefs)
  omega

/-- Appending a scalar source reference and installing the corresponding
singleton closure array preserves the store relation. -/
theorem storeRel_allocRef (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) (value : FlatSem.Value)
    (targetValue : ClosSem.Value) (stores : StoreRel refs targetRefs) (related : ValueRel value targetValue) :
    StoreRel (refs ++ [.refv value])
      (targetRefs.updateEq (refs.length, .valueArray [targetValue])) := by
  intro index
  have original := stores index
  by_cases same : index = refs.length
  · subst index
    simp [HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, related]
  · have different : refs.length ≠ index := Ne.symm same
    by_cases bound : index < refs.length
    · simpa [List.getElem?_append, bound, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, same, different] using original
    · have past : refs.length + 1 ≤ index := by omega
      have originalNone : refs[index]? = none := List.getElem?_eq_none (by omega)
      have originalFree : targetRefs.lookup index = none := by simpa [originalNone] using original
      simpa [List.getElem?_append, bound, past, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL,
        same, different] using originalFree

/-- Allocate related scalar references in related states. -/
theorem stateRel_allocRef {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (value : FlatSem.Value) (targetValue : ClosSem.Value)
    (states : StateRel source target) (related : ValueRel value targetValue) :
    StateRel { source with refs := source.refs ++ [.refv value] }
      { target with refs := target.refs.updateEq (source.refs.length, .valueArray [targetValue]) } := by
  rcases states with ⟨maxApp, ffi, clock, stores, globals, values, install⟩
  exact ⟨maxApp, ffi, clock, storeRel_allocRef source.refs target.refs value targetValue stores related,
    globals, values, install⟩

/-- Updating a scalar reference with related contents preserves the store
relation. -/
theorem storeRel_setRef (refs : Store FlatSem.Value)
    (targetRefs : HolFiniteMapExact Nat (ClosSem.Ref ClosSem.Value)) (index : Nat)
    (old value : FlatSem.Value) (targetValue : ClosSem.Value)
    (stores : StoreRel refs targetRefs) (found : refs[index]? = some (.refv old))
    (related : ValueRel value targetValue) :
    StoreRel (refs.set index (.refv value)) (targetRefs.updateEq (index, .valueArray [targetValue])) := by
  have bound : index < refs.length := (List.getElem?_eq_some_iff.mp found).choose
  intro key
  by_cases same : index = key
  · subst key
    simp [bound, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL, related]
  · have previous := stores key
    simpa [List.getElem?_set, same, Ne.symm same, HolFiniteMapExact.lookup_updateEq, Flapjack.FUPDATE_HOL] using previous

/-- Assignment of related values to a related scalar reference preserves
states and produces the related unit value. -/
theorem assignRef_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (flag : Bool) (index : Nat) (old value : FlatSem.Value) (targetValue : ClosSem.Value)
    (states : StateRel source target) (related : ValueRel value targetValue)
    (found : source.refs[index]? = some (.refv old)) :
    ∃ targetNext,
      FlatSem.doAppMemory source .opassign [.loc flag index, value] =
        some (some ({ source with refs := source.refs.set index (.refv value) }, .val FlatSem.unitValue)) ∧
      ClosSem.applyMemory .update [.refPtr flag index, .number 0, targetValue] target =
        some (ClosSem.unitValue, targetNext) ∧
      StateRel { source with refs := source.refs.set index (.refv value) } targetNext := by
  have stores := states.2.2.2.1
  have slot := stores index
  simp only [found] at slot
  obtain ⟨oldTarget, targetFound, _⟩ := slot
  have newStores := storeRel_setRef source.refs target.refs index old value targetValue stores found related
  refine ⟨{ target with refs := target.refs.updateEq (index, .valueArray [targetValue]) }, ?_, ?_, ?_⟩
  · simp [FlatSem.doAppMemory, storeAssign, found, storeValueSameType]
  · simp [ClosSem.applyMemory, targetFound]
  · rcases states with ⟨maxApp, ffi, clock, _, globals, values, install⟩
    exact ⟨maxApp, ffi, clock, newStores, globals, values, install⟩

end Flapjack.Compiler.Backend.FlatToClos

import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ValueGrowth

/-! Target-only reference growth for mutual closure allocation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- Extending target references preserves the unrelocated-reference frame
when the relocation map is unchanged. -/
theorem unmappedRefsSubmap_of_extension
    (old new : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (f : HolFiniteMapExact Nat Nat)
    (extension : ∀ key value, old.lookup key = some value → new.lookup key = some value) :
    unmappedRefsSubmap old new f f := by
  intro key value lookup fresh
  exact ⟨extension key value lookup, fresh⟩

/-- A reference cell remains related when its contained values remain related. -/
theorem refRel_mono {R S : ClosSem.Value → BvlSem.Value → Prop}
    (preserves : ∀ a b, R a b → S a b) (source : ClosSem.Ref ClosSem.Value)
    (target : BvlSem.Ref BvlSem.Value) (related : refRel R source target) : refRel S source target := by
  cases source <;> cases target <;> simp only [refRel] at related ⊢
  all_goals try exact related
  all_goals try exact related.imp preserves
  all_goals exact ⟨related.1, preserves _ _ related.2⟩

/-- Extending the target store without changing existing references preserves
the candidate state relation. This untagged helper is used by allocation of
mutual-closure environments and does not claim reviewed HOL correspondence. -/
theorem stateRel_targetRefs_extend {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (newRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (states : stateRel f s t)
    (extension : ∀ key value, t.refs.lookup key = some value → newRefs.lookup key = some value) :
    stateRel f s { t with refs := newRefs } := by
  obtain ⟨ffi, globals, table, injective, notFrozen, sourceDomain, targetDomain, cells,
    generic, partialCode, force, oracle, code⟩ := states
  have submap : relocationSubmap f f := by intro key value found; exact found
  have frame := unmappedRefsSubmap_of_extension t.refs newRefs f extension
  have valuesGrow : ∀ a b, vRel s.maxApp f t.refs t.code a b → vRel s.maxApp f newRefs t.code a b := by
    intro a b related
    exact vRel_grow_refs related submap frame
  refine ⟨ffi, ?_, table, injective, ?_, sourceDomain, ?_, ?_, generic, partialCode, force, oracle, code⟩
  · apply globals.imp
    intro source target related
    cases source <;> cases target <;> simp only [optionValueRel] at related ⊢
    exact valuesGrow _ _ related
  · intro x y bytes mapped newFrozen
    have occupied := targetDomain x y mapped
    obtain ⟨cell, oldLookup⟩ := Option.ne_none_iff_exists.mp occupied
    have newLookup := extension y cell oldLookup.symm
    rw [newFrozen] at newLookup
    have equal : cell = .byteArray true bytes := by simpa using newLookup.symm
    subst cell
    exact notFrozen x y bytes mapped oldLookup.symm
  · intro x y mapped
    obtain ⟨cell, oldLookup⟩ := Option.ne_none_iff_exists.mp (targetDomain x y mapped)
    rw [extension y cell oldLookup.symm]
    simp
  · intro index source found
    obtain ⟨target, ptr, mapped, targetLookup, cellRel⟩ := cells index source found
    exact ⟨target, ptr, mapped, extension ptr target targetLookup,
      refRel_mono valuesGrow source target cellRel⟩

/-- Allocating an unused target-only reference preserves the state relation,
the unmapped-reference frame, and freshness with respect to the relocation
map. The allocated value may be any target reference cell. -/
theorem stateRel_targetRefs_update_fresh {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (ptr : Nat) (cell : BvlSem.Ref BvlSem.Value)
    (states : stateRel f s t) (unused : t.refs.lookup ptr = none) :
    stateRel f s { t with refs := t.refs.updateEq (ptr, cell) } ∧
    unmappedRefsSubmap t.refs (t.refs.updateEq (ptr, cell)) f f ∧
    (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
    (t.refs.updateEq (ptr, cell)).lookup ptr = some cell := by
  have outside : ¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr := by
    rintro ⟨sourcePtr, mapped⟩
    have occupied := states.2.2.2.2.2.2.1 sourcePtr ptr mapped
    exact occupied unused
  have extension : ∀ key value, t.refs.lookup key = some value →
      (t.refs.updateEq (ptr, cell)).lookup key = some value := by
    intro key value found
    have different : key ≠ ptr := by
      intro equal
      subst key
      rw [unused] at found
      contradiction
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found
  exact ⟨stateRel_targetRefs_extend s t f _ states extension,
    unmappedRefsSubmap_of_extension t.refs _ f extension, outside,
    by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]⟩

/-- Replacing a target-only cell at an originally unused address preserves
all original references even after earlier target-only extensions. This
supports filling the shared array during recursive-closure construction. -/
theorem stateRel_targetRefs_update_originally_fresh {C F : Type}
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (current : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (ptr : Nat) (cell : BvlSem.Ref BvlSem.Value)
    (states : stateRel f s t) (unused : t.refs.lookup ptr = none)
    (extension : ∀ key value, t.refs.lookup key = some value → current.lookup key = some value) :
    stateRel f s { t with refs := current.updateEq (ptr, cell) } ∧
    unmappedRefsSubmap t.refs (current.updateEq (ptr, cell)) f f ∧
    (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
    (current.updateEq (ptr, cell)).lookup ptr = some cell := by
  have outside : ¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr := by
    rintro ⟨sourcePtr, mapped⟩
    have occupied := states.2.2.2.2.2.2.1 sourcePtr ptr mapped
    exact occupied unused
  have newExtension : ∀ key value, t.refs.lookup key = some value →
      (current.updateEq (ptr, cell)).lookup key = some value := by
    intro key value found
    have different : key ≠ ptr := by
      intro equal
      subst key
      rw [unused] at found
      contradiction
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using extension key value found
  exact ⟨stateRel_targetRefs_extend s t f _ states newExtension,
    unmappedRefsSubmap_of_extension t.refs _ f newExtension, outside,
    by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]⟩

/-- The evaluator's least-unused address meets the target-only allocation
conditions. -/
theorem stateRel_targetRefs_allocate {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (cell : BvlSem.Ref BvlSem.Value) (states : stateRel f s t) :
    let ptr := BvlSem.leastUnusedRef t.refs
    stateRel f s { t with refs := t.refs.updateEq (ptr, cell) } ∧
    unmappedRefsSubmap t.refs (t.refs.updateEq (ptr, cell)) f f ∧
    (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
    (t.refs.updateEq (ptr, cell)).lookup ptr = some cell := by
  exact stateRel_targetRefs_update_fresh s t f (BvlSem.leastUnusedRef t.refs) cell states
    (BvlSem.leastUnusedRef_unused t.refs)

/-- The BVL reference primitive allocates the shared target-only array at the
least unused address while preserving the source-to-target state relation. -/
theorem doApp_allocate_targetOnly {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (values : List BvlSem.Value) (states : stateRel f s t) :
    let ptr := BvlSem.leastUnusedRef t.refs
    let next := { t with refs := t.refs.updateEq (ptr, .valueArray values) }
    BvlSem.doApp (.memOp .ref) values t = .val (.refPtr true ptr, next) ∧
    stateRel f s next ∧ unmappedRefsSubmap t.refs next.refs f f ∧
    (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧ next.refs.lookup ptr = some (.valueArray values) := by
  refine ⟨?_, stateRel_targetRefs_allocate s t f (.valueArray values) states⟩
  simp [BvlSem.doApp, BvlSem.applyMemory]

/-- Updating an in-bounds element of a target-only array preserves the
original state and reference relations, even after earlier updates to that
fresh array. -/
theorem doApp_update_targetOnly {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (current : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (ptr index : Nat) (values : List BvlSem.Value) (value : BvlSem.Value) (flag : Bool)
    (states : stateRel f s t) (unused : t.refs.lookup ptr = none)
    (extension : ∀ key cell, t.refs.lookup key = some cell → current.lookup key = some cell)
    (lookup : current.lookup ptr = some (.valueArray values)) (bound : index < values.length) :
    let start := { t with refs := current }
    let next := { t with refs := current.updateEq (ptr, .valueArray (values.set index value)) }
    BvlSem.doApp (.memOp .update) [.refPtr flag ptr, .number (Int.ofNat index), value] start =
      .val (BvlSem.unitValue, next) ∧
    stateRel f s next ∧ unmappedRefsSubmap t.refs next.refs f f ∧
    (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
    next.refs.lookup ptr = some (.valueArray (values.set index value)) := by
  refine ⟨?_, stateRel_targetRefs_update_originally_fresh s t f current ptr (.valueArray (values.set index value))
    states unused extension⟩
  have nonnegative : ¬ ((index : Int) < 0) := by omega
  have inBounds : ¬ values.length ≤ index := by omega
  simp [BvlSem.doApp, BvlSem.applyMemory, lookup, nonnegative, inBounds]

end Flapjack.Compiler.Backend.ClosToBvl

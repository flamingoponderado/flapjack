module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.ValueGrowth

@[expose] public section

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

/-- A pointwise implication lifts to optional-value relations. This general
helper supports the reference-store growth proofs. -/
theorem optionValueRel_mono {R S : ClosSem.Value → BvlSem.Value → Prop}
    {x : Option ClosSem.Value} {y : Option BvlSem.Value}
    (preserves : ∀ a b, R a b → S a b) (related : optionValueRel R x y) :
    optionValueRel S x y := by
  cases x <;> cases y <;> simp only [optionValueRel] at related ⊢
  exact preserves _ _ related

/-- A fresh target reference preserves the relation between optional values. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "OPTREL_v_rel_NEW_REF"
  (fmap_as_finite_support_relation := [f, refs])]
theorem optionValueRel_newRef (maxApp : Nat) (f : HolFiniteMapExact Nat Nat)
    (refs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (code : Spt (Nat × Bvl.Exp))
    (x : Option ClosSem.Value) (y : Option BvlSem.Value) (r : Nat)
    (cell : BvlSem.Ref BvlSem.Value)
    (premises : optionValueRel (vRel maxApp f refs code) x y ∧ refs.lookup r = none) :
    optionValueRel (vRel maxApp f (refs.updateEq (r, cell)) code) x y := by
  obtain ⟨related, fresh⟩ := premises
  have extension : ∀ key value, refs.lookup key = some value →
      (refs.updateEq (r, cell)).lookup key = some value := by
    intro key value found
    have different : key ≠ r := by
      intro eq
      subst key
      rw [fresh] at found
      contradiction
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found
  have frame := unmappedRefsSubmap_of_extension refs _ f extension
  have submap : f.submap f := by intro key value found; exact found
  exact optionValueRel_mono (fun _ _ rel => vRel_grow_refs rel submap frame) related

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
  have submap : f.submap f := by intro key value found; exact found
  have frame := unmappedRefsSubmap_of_extension t.refs newRefs f extension
  have valuesGrow : ∀ a b, vRel s.maxApp f t.refs t.code a b → vRel s.maxApp f newRefs t.code a b := by
    intro a b related
    exact vRel_grow_refs related submap frame
  refine ⟨ffi, ?_, table, injective, ?_, sourceDomain, ?_, ?_, generic, partialCode, force, oracle, code⟩
  · apply globals.imp
    intro source target related
    exact optionValueRel_mono valuesGrow related
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

namespace FreshTargetRefHOL

/-- The source and target state maps use their canonical finite-support carriers. -/
theorem holFmapAsFiniteSupportRelationWitness_ClosSem.State {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness

/-- The target state maps use their canonical finite-support carrier. -/
theorem holFmapAsFiniteSupportRelationWitness_BvlSem.State {C F : Type} :
    (∀ s : BvlSem.StateBroad C F, (BvlSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : BvlSem.State C F, BvlSem.State.ofBroad s.toBroad = s) :=
  BvlSem.holFmapAsFiniteSupportWitness

/-- Adding a fresh target reference preserves the closure-to-BVL state relation. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "state_rel_NEW_REF"
  (fmap_as_finite_support_relation := [ClosSem.State.refs, ClosSem.State.code, BvlSem.State.refs, f])]
theorem stateRel_newRef {C F : Type} (f : HolFiniteMapExact Nat Nat)
    (s : ClosSem.State C F) (t : BvlSem.State C F) (ptr : Nat)
    (cell : BvlSem.Ref BvlSem.Value)
    (states : stateRel f s t ∧ t.refs.lookup ptr = none) :
    stateRel f s { t with refs := t.refs.updateEq (ptr, cell) } := by
  apply stateRel_targetRefs_extend s t f _ states.1
  intro key value found
  have different : key ≠ ptr := by
    intro equal
    subst key
    rw [states.2] at found
    contradiction
  simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, different] using found

end FreshTargetRefHOL

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
  exact ⟨FreshTargetRefHOL.stateRel_newRef f s t ptr cell ⟨states, unused⟩,
    unmappedRefsSubmap_of_extension t.refs _ f extension, outside,
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

end Flapjack.Compiler.Backend.ClosToBvl

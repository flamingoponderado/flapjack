import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshTargetRefs

/-! Simultaneous source and target reference allocation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL

/-- Adding a pair of fresh pointers extends the relocation map and preserves
the target-only reference frame. -/
theorem freshMapped_growth {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (sourcePtr targetPtr : Nat) (targetCell : BvlSem.Ref BvlSem.Value)
    (states : stateRel f s t) (sourceFree : s.refs.lookup sourcePtr = none)
    (targetFree : t.refs.lookup targetPtr = none) :
    let newMap := f.updateEq (sourcePtr, targetPtr)
    let newRefs := t.refs.updateEq (targetPtr, targetCell)
    relocationSubmap f newMap ∧ unmappedRefsSubmap t.refs newRefs f newMap := by
  have mapFree : f.lookup sourcePtr = none := by
    have domain := states.2.2.2.2.2.1 sourcePtr
    by_contra nonempty
    exact (domain.mp nonempty) sourceFree
  constructor
  · intro key value found
    have ne : key ≠ sourcePtr := by
      intro eq
      subst key
      rw [mapFree] at found
      contradiction
    simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found
  · intro key value found fresh
    have ne : key ≠ targetPtr := by
      intro eq
      subst key
      rw [targetFree] at found
      contradiction
    constructor
    · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ne] using found
    · rintro ⟨ptr, mapped⟩
      by_cases eq : ptr = sourcePtr
      · subst ptr
        simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at mapped
        exact ne mapped.symm
      · have old : f.lookup ptr = some key := by
          simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using mapped
        exact fresh ⟨ptr, old⟩

/-- Allocating related cells at fresh source and target addresses preserves
the candidate state relation under the extended relocation map. -/
theorem stateRel_alloc_mapped {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (sourcePtr targetPtr : Nat)
    (sourceCell : ClosSem.Ref ClosSem.Value) (targetCell : BvlSem.Ref BvlSem.Value)
    (states : stateRel f s t) (sourceFree : s.refs.lookup sourcePtr = none)
    (targetFree : t.refs.lookup targetPtr = none)
    (notFrozen : ∀ bytes, targetCell ≠ .byteArray true bytes)
    (cellRelated : refRel (vRel s.maxApp (f.updateEq (sourcePtr, targetPtr))
      (t.refs.updateEq (targetPtr, targetCell)) t.code) sourceCell targetCell) :
    stateRel (f.updateEq (sourcePtr, targetPtr))
      { s with refs := s.refs.updateEq (sourcePtr, sourceCell) }
      { t with refs := t.refs.updateEq (targetPtr, targetCell) } := by
  obtain ⟨submap, frame⟩ := freshMapped_growth s t f sourcePtr targetPtr targetCell states sourceFree targetFree
  obtain ⟨ffi, globals, table, injective, noFrozen, sourceDomain, targetDomain, cells,
    generic, partialCode, force, oracle, code⟩ := states
  have outOfRange : ∀ ptr, f.lookup ptr ≠ some targetPtr := by
    intro ptr mapped
    exact targetDomain ptr targetPtr mapped targetFree
  have grow : ∀ a b, vRel s.maxApp f t.refs t.code a b →
      vRel s.maxApp (f.updateEq (sourcePtr, targetPtr)) (t.refs.updateEq (targetPtr, targetCell)) t.code a b := by
    intro a b rel
    exact vRel_grow_refs rel submap frame
  refine ⟨ffi, ?_, table, ?_, ?_, ?_, ?_, ?_, generic, partialCode, force, oracle, code⟩
  · apply globals.imp
    intro a b rel
    cases a <;> cases b <;> simp only [optionValueRel] at rel ⊢
    exact grow _ _ rel
  · intro x₁ x₂ y first second
    by_cases a : x₁ = sourcePtr <;> by_cases b : x₂ = sourcePtr
    · exact a.trans b.symm
    · subst x₁
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at first
      subst y
      have old : f.lookup x₂ = some targetPtr := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, b] using second
      exact False.elim (outOfRange x₂ old)
    · subst x₂
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at second
      subst y
      have old : f.lookup x₁ = some targetPtr := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, a] using first
      exact False.elim (outOfRange x₁ old)
    · apply injective x₁ x₂ y
      · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, a] using first
      · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, b] using second
  · intro x y bytes mapped frozen
    by_cases eq : x = sourcePtr
    · subst x
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at mapped
      subst y
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at frozen
      exact notFrozen bytes frozen
    · have old : f.lookup x = some y := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using mapped
      have yNe : y ≠ targetPtr := by
        intro same
        subst y
        exact outOfRange x old
      have oldFrozen : t.refs.lookup y = some (.byteArray true bytes) := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, yNe] using frozen
      exact noFrozen x y bytes old oldFrozen
  · intro x
    by_cases eq : x = sourcePtr
    · subst x
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using sourceDomain x
  · intro x y mapped
    by_cases eq : x = sourcePtr
    · subst x
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at mapped
      subst y
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · have old : f.lookup x = some y := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using mapped
      have yNe : y ≠ targetPtr := by
        intro same
        subst y
        exact outOfRange x old
      simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, yNe] using targetDomain x y old
  · intro x source found
    by_cases eq : x = sourcePtr
    · subst x
      simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] at found
      subst source
      refine ⟨targetCell, targetPtr, ?_, ?_, cellRelated⟩ <;>
        simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    · have oldFound : s.refs.lookup x = some source := by
        simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, eq] using found
      obtain ⟨target, ptr, mapped, targetFound, rel⟩ := cells x source oldFound
      have ptrNe : ptr ≠ targetPtr := by
        intro same
        subst ptr
        exact outOfRange x mapped
      refine ⟨target, ptr, ?_, ?_, refRel_mono grow source target rel⟩
      · exact submap x ptr mapped
      · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ptrNe] using targetFound

/-- Allocating corresponding value arrays extends the relocation map and
returns related source and target pointers. -/
theorem alloc_valueArray_related {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (sourceValues : List ClosSem.Value) (targetValues : List BvlSem.Value)
    (states : stateRel f s t)
    (values : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceValues targetValues) :
    let sourcePtr := ClosSem.leastUnusedRef s.refs
    let targetPtr := BvlSem.leastUnusedRef t.refs
    let newMap := f.updateEq (sourcePtr, targetPtr)
    let sourceNext := { s with refs := s.refs.updateEq (sourcePtr, .valueArray sourceValues) }
    let targetNext := { t with refs := t.refs.updateEq (targetPtr, .valueArray targetValues) }
    stateRel newMap sourceNext targetNext ∧
    vRel s.maxApp newMap targetNext.refs targetNext.code (.refPtr true sourcePtr) (.refPtr true targetPtr) ∧
    relocationSubmap f newMap ∧ unmappedRefsSubmap t.refs targetNext.refs f newMap := by
  let sourcePtr := ClosSem.leastUnusedRef s.refs
  let targetPtr := BvlSem.leastUnusedRef t.refs
  have sourceFree : s.refs.lookup sourcePtr = none := ClosSem.leastUnusedRef_unused s.refs
  have targetFree : t.refs.lookup targetPtr = none := BvlSem.leastUnusedRef_unused t.refs
  have ⟨submap, frame⟩ := freshMapped_growth s t f sourcePtr targetPtr (.valueArray targetValues)
    states sourceFree targetFree
  have grown : List.Forall₂ (vRel s.maxApp (f.updateEq (sourcePtr, targetPtr))
      (t.refs.updateEq (targetPtr, .valueArray targetValues)) t.code) sourceValues targetValues :=
    values.imp (fun _ _ relation => vRel_grow_refs relation submap frame)
  refine ⟨stateRel_alloc_mapped s t f sourcePtr targetPtr (.valueArray sourceValues) (.valueArray targetValues)
      states sourceFree targetFree (by simp) grown, ?_, submap, frame⟩
  exact .refPtr (by simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL])

/-- The source and BVL reference primitives allocate corresponding arrays. -/
theorem doApp_ref_related {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (sourceValues : List ClosSem.Value) (targetValues : List BvlSem.Value)
    (states : stateRel f s t)
    (values : List.Forall₂ (vRel s.maxApp f t.refs t.code) sourceValues targetValues) :
    let sourcePtr := ClosSem.leastUnusedRef s.refs
    let targetPtr := BvlSem.leastUnusedRef t.refs
    let newMap := f.updateEq (sourcePtr, targetPtr)
    let sourceNext := { s with refs := s.refs.updateEq (sourcePtr, .valueArray sourceValues) }
    let targetNext := { t with refs := t.refs.updateEq (targetPtr, .valueArray targetValues) }
    ClosSem.doApp (.memOp .ref) sourceValues s = .val (.refPtr true sourcePtr, sourceNext) ∧
    BvlSem.doApp (.memOp .ref) targetValues t = .val (.refPtr true targetPtr, targetNext) ∧
    stateRel newMap sourceNext targetNext ∧
    vRel s.maxApp newMap targetNext.refs targetNext.code (.refPtr true sourcePtr) (.refPtr true targetPtr) ∧
    relocationSubmap f newMap ∧ unmappedRefsSubmap t.refs targetNext.refs f newMap := by
  refine ⟨?_, ?_, alloc_valueArray_related s t f sourceValues targetValues states values⟩
  · simp [ClosSem.doApp, ClosSem.applyMemory]
  · simp [BvlSem.doApp, BvlSem.applyMemory]

/-- Array allocation with a nonnegative length repeats related initial values
and allocates corresponding fresh cells. -/
theorem doApp_refArray_related {C F : Type} (s : ClosSem.State C F) (t : BvlSem.State C F)
    (f : HolFiniteMapExact Nat Nat) (count : Int) (nonnegative : ¬ count < 0)
    (sourceValue : ClosSem.Value) (targetValue : BvlSem.Value) (states : stateRel f s t)
    (valueRel : vRel s.maxApp f t.refs t.code sourceValue targetValue) :
    let sourcePtr := ClosSem.leastUnusedRef s.refs
    let targetPtr := BvlSem.leastUnusedRef t.refs
    let newMap := f.updateEq (sourcePtr, targetPtr)
    let sourceValues := List.replicate count.toNat sourceValue
    let targetValues := List.replicate count.toNat targetValue
    let sourceNext := { s with refs := s.refs.updateEq (sourcePtr, .valueArray sourceValues) }
    let targetNext := { t with refs := t.refs.updateEq (targetPtr, .valueArray targetValues) }
    ClosSem.doApp (.memOp .refArray) [.number count, sourceValue] s = .val (.refPtr true sourcePtr, sourceNext) ∧
    BvlSem.doApp (.memOp .refArray) [.number count, targetValue] t = .val (.refPtr true targetPtr, targetNext) ∧
    stateRel newMap sourceNext targetNext ∧
    vRel s.maxApp newMap targetNext.refs targetNext.code (.refPtr true sourcePtr) (.refPtr true targetPtr) ∧
    relocationSubmap f newMap ∧ unmappedRefsSubmap t.refs targetNext.refs f newMap := by
  have related : List.Forall₂ (vRel s.maxApp f t.refs t.code)
      (List.replicate count.toNat sourceValue) (List.replicate count.toNat targetValue) := by
    induction count.toNat with
    | zero => exact .nil
    | succ n ih => exact .cons valueRel ih
  refine ⟨?_, ?_, alloc_valueArray_related s t f _ _ states related⟩
  · simp [ClosSem.doApp, ClosSem.applyMemory, nonnegative]
  · simp [BvlSem.doApp, BvlSem.applyMemory, nonnegative]

/-- Successful repeated-array allocation has a nonnegative length and one
initial value. -/
theorem refArray_success {C F : Type} (args : List ClosSem.Value)
    (s next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.doApp (.memOp .refArray) args s = .val (value, next)) :
    ∃ (count : Int) (initial : ClosSem.Value), args = [.number count, initial] ∧ ¬ count < 0 ∧
      value = .refPtr true (ClosSem.leastUnusedRef s.refs) ∧
      next = { s with refs := s.refs.updateEq (ClosSem.leastUnusedRef s.refs,
        .valueArray (List.replicate count.toNat initial)) } := by
  cases args with
  | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
  | cons first rest =>
    cases rest with
    | nil => simp [ClosSem.doApp, ClosSem.applyMemory] at run
    | cons second rest =>
      cases rest with
      | cons third rest => simp [ClosSem.doApp, ClosSem.applyMemory] at run
      | nil =>
        cases first <;> simp only [ClosSem.doApp, ClosSem.applyMemory] at run
        all_goals try contradiction
        case number count =>
          by_cases negative : count < 0
          · simp [negative] at run
          · simp [negative] at run
            exact ⟨count, second, rfl, negative, run.1.symm, run.2.symm⟩

/-- Failed repeated-array allocation reports a source type error. -/
theorem refArray_error {C F : Type} (args : List ClosSem.Value)
    (s : ClosSem.State C F) (error : ErrorResult ClosSem.Value)
    (run : ClosSem.doApp (.memOp .refArray) args s = .err error) : error = .abort .typeError := by
  simp only [ClosSem.doApp] at run
  cases h : ClosSem.applyMemory .refArray args s <;> simp [h] at run
  exact run.symm

end Flapjack.Compiler.Backend.ClosToBvl

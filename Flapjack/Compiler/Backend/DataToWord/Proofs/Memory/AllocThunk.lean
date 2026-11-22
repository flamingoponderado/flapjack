module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.UpdateThunk
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshRefStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.RefMemory

@[expose] public section

/-!
# Allocating a thunk

Counterparts of `v_inv_new_Thunk_insert_lemma`, `v_inv_new_Thunk_insert`,
`blocks_unique_new_thunk` and `new_thunk_thm` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
`ptr ∉ FDOM f` is `¬ mapDomain f ptr` and `ptr ∉ domain refs` is
`¬ sptDomain refs ptr`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Inserting a cell at a fresh key keeps every non-thunk value a non-thunk.
Flapjack proof infrastructure. -/
theorem destThunk_notThunk_insertFresh (value : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (ptr : Nat)
    (cell : BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)
    (fresh : sptLookup ptr refs = none) (notThunk : destThunk value refs = .notThunk) :
    destThunk value (sptInsert ptr cell refs) = .notThunk := by
  cases value with
  | refPtr bit index =>
    by_cases same : index = ptr
    · subst index
      simp [destThunk, fresh] at notThunk
    · simpa [destThunk, sptLookup_sptInsert_ne ptr index _ refs same] using notThunk
  | number _ | block _ _ _ | codePtr _ | word64 _ => simp [destThunk]

/-- The clocked value invariant survives inserting a thunk at a key that is
neither a reference nor in the heap-address map. Flapjack proof
infrastructure for `v_inv_new_Thunk_insert_lemma`. -/
theorem clockValueInv_freshThunk {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ev : AstHOL.ThunkMode)
    (h : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (f tf : HolFiniteMapExact Nat Nat)
    (heap : ValueHeap width) (ptr : Nat) (noMap : ¬ mapDomain f ptr) (fresh : sptLookup ptr refs = none) :
    ∀ ck v1 x, ClockValueInv ck conf v1 refs (x, f, tf, heap) →
      ClockValueInv ck conf v1 (sptInsert ptr (.thunk ev h) refs) (x, f, tf, heap) := by
  intro ck
  induction ck using Nat.strongRecOn with
  | ind ck ih =>
    intro v1 x related
    cases related with
    | numberSmall _ _ i _ _ _ _ small => exact .numberSmall ck conf i _ f tf heap small
    | numberBig _ _ i address _ _ _ _ large cell => exact .numberBig ck conf i address _ f tf heap large cell
    | word64 _ _ word address _ _ _ _ cell => exact .word64 ck conf word address _ f tf heap cell
    | codePtr _ _ n _ _ _ _ => exact .codePtr ck conf n _ f tf heap
    | refPtr bit _ _ n _ _ _ _ domain notThunk notMut =>
      have different : n ≠ ptr := by
        intro same
        subst same
        exact noMap domain
      have lookupEq : sptLookup n (sptInsert ptr (.thunk ev h) refs) = sptLookup n refs :=
        sptLookup_sptInsert_ne ptr n _ refs different
      have result := ClockValueInv.refPtr bit ck conf n (sptInsert ptr (.thunk ev h) refs) f tf heap domain
        (by intro mode body; rw [lookupEq]; exact notThunk mode body)
        (by intro tag finalised left body right lookup; rw [lookupEq] at lookup
            exact notMut tag finalised left body right lookup)
      rwa [lookupEq] at result
    | refPtrThunk _ _ mode n body addr _ _ _ _ cellFound cellEvaluated domain cell recursive =>
      have different : n ≠ ptr := by
        intro same
        subst same
        exact noMap domain
      have lookupEq : sptLookup n (sptInsert ptr (.thunk ev h) refs) = sptLookup n refs :=
        sptLookup_sptInsert_ne ptr n _ refs different
      refine .refPtrThunk ck conf mode n body addr _ f tf heap (by rw [lookupEq]; exact cellFound)
        (fun e => destThunk_notThunk_insertFresh body refs ptr _ fresh (cellEvaluated e)) domain cell ?_
      intro positive
      exact ih (ck - 1) (by omega) body addr (recursive positive)
    | refPtrThunkInlined _ _ n body addr _ _ _ _ cellFound notThunk recursive =>
      have different : n ≠ ptr := by
        intro same
        subst same
        rw [fresh] at cellFound
        cases cellFound
      have lookupEq : sptLookup n (sptInsert ptr (.thunk ev h) refs) = sptLookup n refs :=
        sptLookup_sptInsert_ne ptr n _ refs different
      refine .refPtrThunkInlined ck conf n body x _ f tf heap (by rw [lookupEq]; exact cellFound)
        (destThunk_notThunk_insertFresh body refs ptr _ fresh notThunk) ?_
      intro positive
      exact ih (ck - 1) (by omega) body x (recursive positive)
    | blockNil _ _ stamp tag values _ _ _ _ empty bound zero =>
      exact .blockNil ck conf stamp tag values _ f tf heap empty bound zero
    | blockCons _ _ stamp tag address values xs _ _ _ _ nonempty recursive timestamp cell =>
      refine .blockCons ck conf stamp tag address values xs _ f tf heap nonempty ?_ timestamp cell
      intro positive
      apply (clockValueListInv_iff _ _ _ _ _ _ _ _).mpr
      apply List.Forall₂.imp _ ((clockValueListInv_iff _ _ _ _ _ _ _ _).mp (recursive positive))
      intro child addr childInv
      exact ih (ck - 1) (by omega) child addr childInv

/-- HOL `v_inv_new_Thunk_insert_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_new_Thunk_insert_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_newThunkInsert_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ev : AstHOL.ThunkMode)
    (h : Flapjack.Compiler.Backend.DataSem.Value) :
    ∀ (ck : Nat) (v : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (ptr : Nat),
      valueInv conf v refs (x, f, tf, heap) ∧ ¬ mapDomain f ptr ∧ ¬ sptDomain refs ptr ∧
          (ev = .evaluated → destThunk h refs = .notThunk) →
        ClockValueInv ck conf v (sptInsert ptr (.thunk ev h) refs) (x, f, tf, heap) := by
  rintro ck v refs x f tf heap ptr ⟨inv, noMap, notRef, _⟩
  have fresh : sptLookup ptr refs = none := by
    cases found : sptLookup ptr refs with
    | none => rfl
    | some cell => exact False.elim (notRef ((sptDomain_iff_lookup refs ptr).mpr ⟨cell, found⟩))
  exact clockValueInv_freshThunk conf ev h refs f tf heap ptr noMap fresh ck v x (inv ck)

/-- HOL `v_inv_new_Thunk_insert`, the unclocked form of
`v_inv_new_Thunk_insert_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_new_Thunk_insert"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_newThunkInsert {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (v : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
    (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (ptr : Nat)
    (ev : AstHOL.ThunkMode) (h : Flapjack.Compiler.Backend.DataSem.Value) :
    valueInv conf v refs (x, f, tf, heap) ∧ ¬ mapDomain f ptr ∧ ¬ sptDomain refs ptr ∧
        (ev = .evaluated → destThunk h refs = .notThunk) →
      valueInv conf v (sptInsert ptr (.thunk ev h) refs) (x, f, tf, heap) := by
  intro valid ck
  exact valueInv_newThunkInsert_lemma conf ev h ck v refs x f tf heap ptr valid

/-- HOL `blocks_unique_new_thunk`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "blocks_unique_new_thunk"]
theorem blocksUnique_newThunk (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (v : Flapjack.Compiler.Backend.DataSem.Value) (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (ptr : Nat) (ev : AstHOL.ThunkMode) :
    blocksUnique ts (allValues refs (v :: stack)) →
      blocksUnique ts (allValues (sptInsert ptr (.thunk ev v) refs) (v :: .refPtr false ptr :: stack)) := by
  intro unique
  apply blocksUnique_updateThunk ts ptr ev refs v stack
  have drop : ∀ s t xs, allValues refs (v :: .refPtr false ptr :: stack) (.block s t xs) →
      allValues refs (v :: stack) (.block s t xs) := by
    intro s t xs member
    rcases member with first | second | third | onStack
    · exact Or.inl first
    · exact Or.inr (Or.inl second)
    · exact Or.inr (Or.inr (Or.inl third))
    · apply Or.inr (Or.inr (Or.inr ?_))
      have split1 : v :: .refPtr false ptr :: stack = [v] ++ ([.refPtr false ptr] ++ stack) := rfl
      have split2 : v :: stack = [v] ++ stack := rfl
      rw [split1, valueListValues_append, valueListValues_append] at onStack
      rw [split2, valueListValues_append]
      simp only [List.mem_append] at onStack ⊢
      rcases onStack with inV | inPtr | inStack
      · exact Or.inl inV
      · simp [valueListValues] at inPtr
      · exact Or.inr inStack
  intro stamp tag1 xs1 tag2 xs2 ⟨h1, n1, h2, n2⟩
  exact unique stamp tag1 xs1 tag2 xs2 ⟨drop _ _ _ h1, n1, drop _ _ _ h2, n2⟩

/-- Allocating a thunk at the end of unused space moves the collector's
reference boundary. Flapjack helper for `new_thunk_thm`, after
`gcKindInv_allocateFreshRef`. -/
theorem gcKindInv_allocateFreshThunk {α β : Type} (conf : DataToWord.Config) (ev : AstHOL.ThunkMode)
    (r : HeapAddress α) (heap heap2 : List (HeapElement α (HeapTag × List β))) (a sp sp1 : Nat) (gens : GenState)
    (fits : 2 ≤ sp)
    (valid : gcKindInv conf a sp sp1 gens heap)
    (store : heapStoreUnused a (sp + sp1) (thunkBlock ev r) heap = (heap2, true))
    (unused : unusedSpaceInv a (sp + sp1 - 2) heap2) :
    gcKindInv conf a (sp - 2) sp1 gens heap2 := by
  cases kind : conf.gcKind with
  | none => simpa [gcKindInv, kind] using valid
  | simple => simpa [gcKindInv, kind] using valid
  | generational sizes =>
    simp only [gcKindInv, kind] at valid ⊢
    obtain ⟨oldGens, first, second, oldSplit, noRefs, refs⟩ := valid
    have newGens := heapStoreUnused_genStateOk a (sp + sp1) (thunkBlock ev r) heap heap2 gens
      ⟨store, by simpa [Nat.add_assoc] using oldGens⟩
    have elemLength : elLength (thunkBlock ev r : HeapElement α (HeapTag × List β)) = 2 := by
      simp [thunkBlock, elLength]
    have unused' : unusedSpaceInv a (sp + sp1 - elLength (thunkBlock ev r : HeapElement α (HeapTag × List β))) heap2 := by
      simpa [elemLength] using unused
    obtain ⟨before, firstEq, whole, aEq, heapEq⟩ := heapStoreUnused_shape a (sp + sp1) heap first second heap2
      (thunkBlock ev r) ⟨by simpa [Nat.add_assoc] using oldSplit, store, unused'⟩
    let newPrefix := before ++ heapExpand (sp + sp1 - 2)
    have newPrefixLength : heapLength newPrefix = a + (sp - 2) + sp1 := by
      simp [newPrefix, heapLength_append, heapLength_heapExpand, aEq]
      omega
    refine ⟨?_, newPrefix, thunkBlock ev r :: second, ?_, ?_, ?_⟩
    · have boundary : a + (sp + sp1) - 2 = a + (sp - 2) + sp1 := by omega
      simpa [elemLength, boundary] using newGens
    · rw [← newPrefixLength, heapEq]
      simpa [newPrefix, elemLength, List.append_assoc] using
        Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.heapSplit_append newPrefix (thunkBlock ev r :: second)
    · intro element member
      simp only [newPrefix, List.mem_append] at member
      rcases member with old | free
      · apply noRefs element
        rw [firstEq]
        exact List.mem_append_left _ old
      · by_cases zero : sp + sp1 - 2 = 0
        · simp [heapExpand, zero] at free
        · simp [heapExpand, zero] at free
          subst element
          simp [isRef]
    · intro element member
      rcases List.mem_cons.mp member with same | old
      · subst element
        simp [isRef, thunkBlock, isMutTag]
      · exact refs element old

/-- Allocate a thunk block and preserve the root, heap and collector
components of the invariant. Flapjack helper for `new_thunk_thm`, after
`heapStoreUnused_freshRef_valid`. -/
theorem heapStoreUnused_freshThunk_valid {α β : Type} (conf : DataToWord.Config) (ev : AstHOL.ThunkMode)
    (a sp sp1 limit : Nat) (gens : GenState)
    (heap : List (HeapElement α (HeapTag × List β))) (r : HeapAddress α) (roots : List (HeapAddress α))
    (zero : α) (unused : unusedSpaceInv a (sp + sp1) heap)
    (fits : 2 ≤ sp) (rootsValid : rootsOk (r :: roots) heap)
    (heapValid : heapOk heap limit) (gcValid : gcKindInv conf a sp sp1 gens heap) :
    ∃ heap2, heapStoreUnused a (sp + sp1) (thunkBlock ev r) heap = (heap2, true) ∧
      unusedSpaceInv a (sp - 2 + sp1) heap2 ∧
      heapLookup (a + sp + sp1 - 2) heap2 = some (thunkBlock ev r) ∧
      ¬ isSomeDataElement (heapLookup (a + sp + sp1 - 2) heap) ∧
      heapStoreRel heap heap2 ∧
      rootsOk (r :: .pointer (a + sp + sp1 - 2) zero :: roots) heap2 ∧
      heapOk heap2 limit ∧ gcKindInv conf a (sp - 2) sp1 gens heap2 := by
  have len : elLength (thunkBlock ev r : HeapElement α (HeapTag × List β)) = 2 := by
    simp [thunkBlock, elLength]
  obtain ⟨heap2, stored, unused2, found, oldNot, lengthEq, forward, members, positions, rel⟩ :=
    heapStoreUnused_exists a (sp + sp1) heap (thunkBlock ev r) unused (by rw [len]; omega)
  have preserved (ptr : Nat) (old : isSomeDataElement (heapLookup ptr heap)) :
      isSomeDataElement (heapLookup ptr heap2) := by
    rw [rel ptr old]
    exact old
  have newGc := gcKindInv_allocateFreshThunk conf ev r heap heap2 a sp sp1 gens fits gcValid stored
    (by simpa [len] using unused2)
  refine ⟨heap2, stored, ?_, ?_, ?_, rel, ?_, ?_, newGc⟩
  · have same : sp + sp1 - 2 = sp - 2 + sp1 := by omega
    simpa [len, same] using unused2
  · simpa [len, Nat.add_assoc] using found
  · simpa [len, Nat.add_assoc] using oldNot
  · intro ptr value member
    rcases List.mem_cons.mp member with equal | inTail
    · exact preserved ptr (rootsValid ptr value (by simp [equal]))
    · rcases List.mem_cons.mp inTail with equal | inRoots
      · cases equal
        rw [show a + sp + sp1 - 2 = a + (sp + sp1) - elLength (thunkBlock ev r : HeapElement α (HeapTag × List β)) by
          rw [len]; omega, found]
        simp [isSomeDataElement, thunkBlock]
      · exact preserved ptr (rootsValid ptr value (List.mem_cons_of_mem _ inRoots))
  · refine ⟨lengthEq.trans heapValid.1, ?_, ?_⟩
    · exact (forward (by simp [isForwardPointer, thunkBlock])).trans heapValid.2.1
    · intro xs l d ptr value ⟨member, pointer⟩
      rcases (members xs l d).mp member with new | old
      · simp only [thunkBlock, HeapElement.dataElement.injEq] at new
        obtain ⟨rfl, _, _⟩ := new
        simp only [List.mem_singleton] at pointer
        exact preserved ptr (rootsValid ptr value (by simp [pointer]))
      · exact preserved ptr (heapValid.2.2 xs l d ptr value ⟨old, pointer⟩)

/-- A directly observed value keeps its invariant after allocating a thunk.
Flapjack helper for `new_thunk_thm`. -/
theorem valueInv_freshThunk {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (refs : Spt (BvlSem.Ref Value)) (ptr a : Nat) (ev : AstHOL.ThunkMode) (h : Value) (stack : List Value)
    (f tf : HolFiniteMapExact Nat Nat) (heap heap2 : ValueHeap width)
    (value : Value) (address : HeapAddress (WordLocW width))
    (fresh : sptLookup ptr refs = none) (freshMap : f.lookup ptr = none)
    (rel : heapStoreRel heap heap2)
    (related : valueInv conf value refs (address, f, tf, heap))
    (observed : (∃ index cell, sptLookup index (sptInsert ptr (.thunk ev h) refs) = some cell ∧
      findRef cell value) ∨ value ∈ stack) :
    valueInv conf value (sptInsert ptr (.thunk ev h) refs)
      (address, f.update (ptr, a), restrictTimestampMap tf (allTimestamps (sptInsert ptr (.thunk ev h) refs) stack),
        heap2) := by
  have noMap : ¬ mapDomain f ptr := by
    rintro ⟨mapped, found⟩
    rw [freshMap] at found
    cases found
  have inserted : valueInv conf value (sptInsert ptr (.thunk ev h) refs) (address, f, tf, heap) := fun ck =>
    clockValueInv_freshThunk conf ev h refs f tf heap ptr noMap fresh ck value address (related ck)
  have fsub : f.submap (f.update (ptr, a)) := by
    intro key result lookup
    have ne : key ≠ ptr := by intro same; subst key; rw [freshMap] at lookup; contradiction
    simpa [HolFiniteMapExact.update, FUPDATE, ne, Ne.symm ne] using lookup
  have extended := valueInv_submap conf _ f (f.update (ptr, a)) tf tf heap heap2 value address
    ⟨fsub, HolFiniteMapExact.submap_refl tf, rel, inserted⟩
  apply valueInv_tfRestrict conf value _ stack address (f.update (ptr, a)) tf heap2 _
  exact ⟨extended, fun stamp member => ⟨value, observed, member⟩, fun _ member => member⟩

/-- Existing reference cells keep their invariants after allocating a thunk.
Flapjack helper for `new_thunk_thm`. -/
theorem bcRefInv_freshThunk_other {width : Nat} [NeZero width] (conf : DataToWord.Config)
    (refs : Spt (BvlSem.Ref Value)) (f tf : HolFiniteMapExact Nat Nat)
    (heap heap2 : ValueHeap width) (be : Bool) (ptr index a : Nat) (ev : AstHOL.ThunkMode) (h : Value)
    (stack : List Value)
    (fresh : sptLookup ptr refs = none) (freshMap : f.lookup ptr = none) (different : index ≠ ptr)
    (rel : heapStoreRel heap heap2) (valid : bcRefInv conf index refs (f, tf, heap, be)) :
    bcRefInv conf index (sptInsert ptr (.thunk ev h) refs)
      (f.update (ptr, a), restrictTimestampMap tf (allTimestamps (sptInsert ptr (.thunk ev h) refs) stack),
        heap2, be) := by
  have lookupRefs : sptLookup index (sptInsert ptr (.thunk ev h) refs) = sptLookup index refs :=
    sptLookup_sptInsert_ne ptr index _ refs different
  have cells : ∀ ptr cell, isDataElement cell → heapLookup ptr heap = some cell → heapLookup ptr heap2 = some cell := by
    intro ptr cell data found
    obtain ⟨xs, len, d, rfl⟩ := data
    exact (rel ptr ⟨xs, len, d, found⟩).trans found
  cases fLookup : f.lookup index with
  | none => simp [bcRefInv, fLookup] at valid
  | some mapped =>
    have fNew : (f.update (ptr, a)).lookup index = some mapped := by
      simpa [HolFiniteMapExact.update, FUPDATE, different, Ne.symm different] using fLookup
    cases refLookup : sptLookup index refs with
    | none => simp [bcRefInv, fLookup, refLookup] at valid
    | some cell =>
      cases cell with
      | valueArray items =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fNew, lookupRefs, refLookup]
        obtain ⟨addresses, cell, related⟩ := valid
        refine ⟨addresses, cells mapped _ (by simp [isDataElement, refBlock]) cell, ?_⟩
        apply List.Forall₂.flip
        apply forall2_imp_member related.flip
        intro value addr member inv
        apply valueInv_freshThunk conf refs ptr a ev h stack f tf heap heap2 value addr fresh freshMap rel inv
        exact Or.inl ⟨index, .valueArray items, by rw [lookupRefs, refLookup], member⟩
      | byteArray flag bytes =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fNew, lookupRefs, refLookup]
        exact cells mapped _ (by simp [isDataElement, bytesRep]) valid
      | thunk mode value =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fNew, lookupRefs, refLookup]
        obtain ⟨addr, cell, safe, inv⟩ := valid
        refine ⟨addr, cells mapped _ (by simp [isDataElement, thunkBlock]) cell, ?_, ?_⟩
        · intro evaluated
          exact destThunk_notThunk_insertFresh value refs ptr _ fresh (safe evaluated)
        · apply valueInv_freshThunk conf refs ptr a ev h stack f tf heap heap2 value addr fresh freshMap rel inv
          exact Or.inl ⟨index, .thunk mode value, by rw [lookupRefs, refLookup], rfl⟩
      | mutBlock tag finalised left value right =>
        simp only [bcRefInv, fLookup, refLookup] at valid
        simp only [bcRefInv, fNew, lookupRefs, refLookup]
        obtain ⟨gen, noStamp, addresses, cell, related⟩ := valid
        refine ⟨gen, ?_, addresses, cells mapped _ (by simp [isDataElement, blockRep]) cell, ?_⟩
        · intro unfinished ⟨stamp, domain, maps⟩
          obtain ⟨oldDomain, sameApply⟩ := restrictTimestampMap_domain_apply tf _ stamp domain
          exact noStamp unfinished ⟨stamp, oldDomain, sameApply.symm.trans maps⟩
        · apply List.Forall₂.flip
          apply forall2_imp_member related.flip
          intro item addr member inv
          apply valueInv_freshThunk conf refs ptr a ev h stack f tf heap heap2 item addr fresh freshMap rel inv
          exact Or.inl ⟨index, .mutBlock tag finalised left value right, by rw [lookupRefs, refLookup], member⟩

/-- Allocating a thunk preserves the stack/reference relation. Flapjack
helper for `new_thunk_thm`, after `bcStackRefInv_freshValueArray`. -/
theorem bcStackRefInv_freshThunk {width : Nat} [NeZero width] (conf : DataToWord.Config) (next : Nat)
    (v : Value) (stack : List Value) (refs : Spt (BvlSem.Ref Value))
    (r : HeapAddress (WordLocW width)) (roots : List (HeapAddress (WordLocW width))) (heap heap2 : ValueHeap width)
    (be : Bool) (ptr a : Nat) (ev : AstHOL.ThunkMode)
    (fresh : sptLookup ptr refs = none) (evaluated : ev = .evaluated → destThunk v refs = .notThunk)
    (oldNot : ¬ isSomeDataElement (heapLookup a heap))
    (rel : heapStoreRel heap heap2) (newCell : heapLookup a heap2 = some (thunkBlock ev r))
    (valid : bcStackRefInv conf next (v :: stack) refs (r :: roots, heap, be)) :
    bcStackRefInv conf next (v :: .refPtr false ptr :: stack) (sptInsert ptr (.thunk ev v) refs)
      (r :: .pointer a (.word 0) :: roots, heap2, be) := by
  obtain ⟨f, tf, injF, domainF, injTf, timestamps, nextBound, endian, unique, related, refsInv⟩ := valid
  have freshMap : f.lookup ptr = none := by
    cases found : f.lookup ptr with
    | none => rfl
    | some mapped =>
      obtain ⟨cell, lookup⟩ := domainF ptr ⟨mapped, found⟩
      simp [fresh] at lookup
  have preserved (index : Nat) (old : isSomeDataElement (heapLookup index heap)) :
      isSomeDataElement (heapLookup index heap2) := by rw [rel index old]; exact old
  have newData : isSomeDataElement (heapLookup a heap2) := by rw [newCell]; simp [isSomeDataElement, thunkBlock]
  have freshTarget : ∀ n, mapDomain f n → holFapply f n ≠ a := by
    intro n domain same
    apply oldNot
    rw [← same]
    exact injF.1 n domain
  have injF1 := freshBlock_timestampMap_injective f ptr a
    (fun p => isSomeDataElement (heapLookup p heap)) (fun p => isSomeDataElement (heapLookup p heap2))
    injF preserved newData freshTarget
  let newRefs := sptInsert ptr (.thunk ev v) refs
  let newStack := v :: .refPtr false ptr :: stack
  let keep := allTimestamps newRefs newStack
  let tf2 := restrictTimestampMap tf keep
  have injTf1 : mapInjInto tf2 (fun p => isSomeDataElement (heapLookup p heap2)) := by
    refine ⟨?_, ?_⟩
    · intro key domain
      obtain ⟨oldDomain, same⟩ := restrictTimestampMap_domain_apply tf keep key domain
      rw [same]
      exact preserved _ (injTf.1 key oldDomain)
    · intro x y ⟨domainX, domainY⟩ equal
      obtain ⟨oldX, sameX⟩ := restrictTimestampMap_domain_apply tf keep x domainX
      obtain ⟨oldY, sameY⟩ := restrictTimestampMap_domain_apply tf keep y domainY
      apply injTf.2 x y ⟨oldX, oldY⟩
      exact sameX.symm.trans (equal.trans sameY)
  have newLookup : (f.update (ptr, a)).lookup ptr = some a := by simp [HolFiniteMapExact.update, FUPDATE]
  have transformed : List.Forall₂ (fun value address => valueInv conf value newRefs
      (address, f.update (ptr, a), tf2, heap2)) (v :: stack) (r :: roots) := by
    apply forall2_imp_member related
    intro value address member inv
    apply valueInv_freshThunk conf refs ptr a ev v newStack f tf heap heap2 value address fresh freshMap rel inv
    right
    rcases List.mem_cons.mp member with first | last
    · simp [newStack, first]
    · simp [newStack, last]
  obtain _ | ⟨headInv, tailInv⟩ := transformed
  have applied : holFapply (f.update (ptr, a)) ptr = a := holFapply_of_lookup newLookup
  have refFound : sptLookup ptr newRefs = some (.thunk ev v) := sptLookup_sptInsert_same _ _ _
  have evaluatedNew : ev = .evaluated → destThunk v newRefs = .notThunk :=
    fun e => destThunk_notThunk_insertFresh v refs ptr _ fresh (evaluated e)
  have cellNew : heapLookup (holFapply (f.update (ptr, a)) ptr) heap2 = some (thunkBlock ev r) := by
    rw [applied]; exact newCell
  refine ⟨f.update (ptr, a), tf2, injF1, ?_, injTf1, ?_, ?_, endian, ?_, ?_, ?_⟩
  · intro n domain
    by_cases same : n = ptr
    · subst n
      exact ⟨.thunk ev v, sptLookup_sptInsert_same _ _ _⟩
    · obtain ⟨mapped, lookup⟩ := domain
      have old : f.lookup n = some mapped := by simpa [HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using lookup
      obtain ⟨cell, found⟩ := domainF n ⟨mapped, old⟩
      exact ⟨cell, by simpa [newRefs, sptLookup_sptInsert_ne ptr n _ refs same] using found⟩
  · intro n domain
    obtain ⟨w, lookup⟩ := domain
    exact ((restrictTimestampMap_lookup_some tf keep n w).mp lookup).1
  · intro n domain
    exact nextBound n (restrictTimestampMap_domain_apply tf keep n domain).1
  · exact blocksUnique_newThunk next refs v stack ptr ev unique
  · refine .cons headInv (.cons ?_ tailInv)
    intro ck
    have head := ClockValueInv.refPtrThunk ck conf ev ptr v r newRefs (f.update (ptr, a)) tf2 heap2 refFound
      evaluatedNew ⟨a, newLookup⟩ cellNew (fun _ => headInv (ck - 1))
    simpa [applied] using head
  · intro n ⟨reachable, domain⟩
    by_cases same : n = ptr
    · subst n
      simp only [bcRefInv, newLookup, sptLookup_sptInsert_same]
      exact ⟨r, newCell, evaluatedNew, headInv⟩
    · obtain ⟨mapped, lookup⟩ := domain
      have oldLookup : f.lookup n = some mapped := by
        simpa [HolFiniteMapExact.update, FUPDATE, same, Ne.symm same] using lookup
      have reachThunk := reachableRefs_thunkUpdate v false ptr stack ev refs n reachable
      have oldReach : reachableRefs (v :: stack) refs n := by
        obtain ⟨value, start, member, reference, path⟩ := reachThunk
        rcases List.mem_cons.mp member with first | rest
        · exact ⟨value, start, by simp [first], reference, path⟩
        rcases List.mem_cons.mp rest with second | inStack
        · subst value
          have startEq : start = ptr := by simpa [getRefs] using reference
          subst start
          rcases Relation.ReflTransGen.cases_head path with same' | ⟨next', edge, _⟩
          · exact False.elim (same same'.symm)
          · simp [refEdge, fresh] at edge
        · exact ⟨value, start, List.mem_cons_of_mem _ inStack, reference, path⟩
      exact bcRefInv_freshThunk_other conf refs f tf heap heap2 be ptr n a ev v newStack fresh freshMap same rel
        (refsInv n ⟨oldReach, ⟨mapped, oldLookup⟩⟩)

/-- HOL `new_thunk_thm`. The three source conjuncts plus the evaluation
condition are the single hypothesis `valid`. HOL's conclusion also binds an
existential `p` of an independent type `β` that occurs nowhere else in the
statement; source review confirms it is vacuous, so it is omitted (as for
the reviewed `memory_rel_Number_bignum_header`). -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "new_thunk_thm"
  (words_as_type_indexed_bitvec)]
theorem newThunk {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (v : Flapjack.Compiler.Backend.DataSem.Value) (stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit ts ptr : Nat) (ev : AstHOL.ThunkMode)
    (valid : absMlInv conf (v :: stack) refs (roots, heap, be, a, sp, sp1, gens) limit ts ∧
      ¬ sptDomain refs ptr ∧ 2 ≤ sp ∧ (ev = .evaluated → destThunk v refs = .notThunk)) :
    ∃ (r : HeapAddress (WordLocW width)) (roots2 : List (HeapAddress (WordLocW width))) (heap2 : ValueHeap width),
      roots = r :: roots2 ∧ heapStoreUnused a (sp + sp1) (thunkBlock ev r) heap = (heap2, true) ∧
      absMlInv conf (v :: .refPtr false ptr :: stack) (sptInsert ptr (.thunk ev v) refs)
        (r :: .pointer (a + sp + sp1 - 2) (.word 0) :: roots2, heap2, be, a, sp - 2, sp1, gens) limit ts := by
  obtain ⟨inv, notRef, fits, evaluated⟩ := valid
  obtain ⟨rootsValid, heapValid, gcValid, unused, stackValid⟩ := inv
  have fresh : sptLookup ptr refs = none := by
    cases found : sptLookup ptr refs with
    | none => rfl
    | some cell => exact False.elim (notRef ((sptDomain_iff_lookup refs ptr).mpr ⟨cell, found⟩))
  obtain ⟨r, roots2, rootsEq⟩ : ∃ r roots2, roots = r :: roots2 := by
    obtain ⟨_, _, _, _, _, _, _, _, _, related, _⟩ := stackValid
    cases related with
    | cons _ _ => exact ⟨_, _, rfl⟩
  subst rootsEq
  obtain ⟨heap2, stored, unused2, found, oldNot, rel, rootsAfter, heapAfter, gcAfter⟩ :=
    heapStoreUnused_freshThunk_valid conf ev a sp sp1 limit gens heap r roots2 (.word 0) unused fits
      rootsValid heapValid gcValid
  have stackAfter := bcStackRefInv_freshThunk conf ts v stack refs r roots2 heap heap2 be ptr
    (a + sp + sp1 - 2) ev fresh evaluated oldNot rel found stackValid
  exact ⟨r, roots2, heap2, rfl, stored, rootsAfter, heapAfter, gcAfter, unused2, stackAfter⟩

/-- The encoded thunk cell is exactly its two words when its header encodes.
Flapjack helper for `memory_rel_AllocThunk`, after `wordElRefEq`. -/
theorem wordElThunkEq {width : Nat} [NeZero width] (c : DataToWord.Config) (ev : AstHOL.ThunkMode)
    (addr : BitVec width) (r : HeapAddress (WordLocW width)) (hd : BitVec width)
    (encoded : encodeHeader c (match ev with | .evaluated => 14 | .notEvaluated => 6) 1 = some hd)
    (configBound : c.lenSize + 5 < width) (good : goodDimindex width) :
    wordEl addr (thunkBlock ev r) c = Misc.wordList addr [.word hd, wordAddr c r] := by
  have header : makeHeader c (((thunkTagToBits ev : BitVec width) <<< (3 : Nat)) ||| 6) 1 = hd := by
    cases ev with
    | evaluated =>
      rw [thunkTagBits_evaluated]
      have h : encodeHeader c 14 1 = some hd := encoded
      simp only [encodeHeader] at h
      split at h
      · exact Option.some.inj h
      · simp at h
    | notEvaluated =>
      have bits : ((thunkTagToBits .notEvaluated : BitVec width) <<< (3 : Nat)) ||| 6 = 6 := by
        simp [thunkTagToBits]
      rw [bits]
      have h : encodeHeader c 6 1 = some hd := encoded
      simp only [encodeHeader] at h
      split at h
      · exact Option.some.inj h
      · simp at h
  have decoded := encodeHeaderImp c _ 1 hd encoded configBound good
  rw [wordEl_thunkUnfold, header]
  funext heap
  apply propext
  simp [decoded.1, decoded.2, StackRemove.WordListExists.starCond]

/-- Store the concrete thunk block and update both free-space boundaries.
Flapjack helper for `memory_rel_AllocThunk`, after
`heapInMemoryStore_allocateRef`. -/
theorem heapInMemoryStore_allocateThunk {width : Nat} [NeZero width]
    (c : DataToWord.Config) (ev : AstHOL.ThunkMode) (heap heap2 : ValueHeap width) (a sp sp1 : Nat)
    (gens : GenState) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool) (limit : Nat)
    (r : HeapAddress (WordLocW width)) (hd : BitVec width)
    (encoded : encodeHeader c (match ev with | .evaluated => 14 | .notEvaluated => 6) 1 = some hd)
    (good : goodDimindex width) (unused : unusedSpaceInv a (sp + sp1) heap) (fits : 2 ≤ sp)
    (stored : heapStoreUnused a (sp + sp1) (thunkBlock ev r) heap = (heap2, true))
    (heapMem : heapInMemoryStore heap a sp sp1 gens c st m dm limit) :
    ∃ eoh trig curr m1, st.lookup .endOfHeap = some (.word eoh) ∧
      st.lookup .triggerGC = some (.word trig) ∧ st.lookup .currHeap = some (.word curr) ∧
      eoh = curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + sp + sp1) ∧
      storeList (eoh - wordSemBytesInWord * BitVec.ofNat width 2) [.word hd, wordAddr c r] m dm = some m1 ∧
      heapInMemoryStore heap2 a (sp - 2) sp1 gens c
        ((st.update (.endOfHeap, .word (eoh - wordSemBytesInWord * BitVec.ofNat width 2))).update
          (.triggerGC, .word (trig - wordSemBytesInWord * BitVec.ofNat width 2))) m1 dm limit := by
  have positive : sp + sp1 ≠ 0 := by omega
  have found := unused.1 positive
  obtain ⟨pre, post, heapShape, aEq⟩ := heapLookup_split heap a _ found
  have expand : (heapExpand (sp + sp1) : ValueHeap width) = [.unused (sp + sp1 - 1)] := by
    unfold heapExpand
    rw [if_neg positive]
  have heapOld : heap = pre ++ heapExpand (sp + sp1) ++ post := by
    simpa [expand, List.append_assoc] using heapShape
  have heap2Shape : heap2 = pre ++ heapExpand (sp + sp1 - 2) ++ [thunkBlock ev r] ++ post := by
    have store := stored
    classical
    simp only [heapStoreUnused, found, show elLength (thunkBlock ev r : HeapElement (WordLocW width)
        (HeapTag × List (WordLocW width))) ≤ sp + sp1 by simp [thunkBlock, elLength]; omega,
      and_self, ↓reduceIte] at store
    rw [heapShape, aEq, heapStore_atPrefix] at store
    have h := congrArg Prod.fst store
    simpa [thunkBlock, elLength, List.append_assoc] using h.symm
  obtain ⟨heapBound, byteBound, shiftBound, lenPos, lenBound, shiftWidth, globals, curr, other,
    currAligned, otherAligned, currLookup, otherLookup, freeLookup, triggerLookup, endLookup,
    heapLenLookup, globInv, genInv, heapSep⟩ := heapMem
  have heapSepOld : SetSep.star (wordHeap curr (pre ++ heapExpand (sp + sp1) ++ post) c)
      (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m, fun x => dm x = true)) := by
    simpa [heapOld] using heapSep
  have configBound : c.lenSize + 5 < width := by omega
  obtain ⟨m1, run, heapSepNew⟩ := wordHeapAllocEnd c curr pre post (sp + sp1) (thunkBlock ev r) [wordAddr c r] hd
    (wordHeap other (heapExpand limit) c) m dm (by simp; omega) (by simp [thunkBlock, elLength])
    (fun addr => wordElThunkEq c ev addr r hd encoded configBound good) heapSepOld
  have nLen : heapLength heap2 = heapLength heap :=
    heapStoreUnused_imp_length a (sp + sp1) (thunkBlock ev r) heap heap2 stored
  let eoh := curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + sp + sp1)
  let trig := curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + sp)
  let step := wordSemBytesInWord * BitVec.ofNat width 2
  let st1 := (st.update (.endOfHeap, .word (eoh - step))).update (.triggerGC, .word (trig - step))
  have boundary : a + sp + sp1 = (a + sp + sp1 - 2) + 2 := by omega
  have boundaryTrig : a + sp = (a + (sp - 2)) + 2 := by omega
  have newEnd : eoh - step = curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + sp + sp1 - 2) := by
    conv_lhs => unfold eoh step
    rw [boundary]
    simp [wordSemBytesInWord, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add, ← BitVec.add_assoc]
  have newTrig : trig - step = curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + (sp - 2)) := by
    conv_lhs => unfold trig step
    rw [boundaryTrig]
    simp [wordSemBytesInWord, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add, ← BitVec.add_assoc]
  have shapeSep : SetSep.star (wordHeap curr heap2 c) (wordHeap other (heapExpand limit) c)
      (SetSep.fun2Set (m1, fun x => dm x = true)) := by simpa [heap2Shape] using heapSepNew
  have heapMem1 : heapInMemoryStore heap2 a (sp - 2) sp1 gens c st1 m1 dm limit := by
    refine ⟨by simpa [nLen] using heapBound, by simpa [nLen] using byteBound, shiftBound, lenPos, lenBound,
      shiftWidth, ?_, curr, other, currAligned, otherAligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, shapeSep⟩
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using globals
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using currLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using otherLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using freeLookup
    · simp [st1, HolFiniteMapExact.update, FUPDATE, newTrig]
    · have arith : a + (sp - 2) + sp1 = a + sp + sp1 - 2 := by omega
      simp [st1, HolFiniteMapExact.update, FUPDATE, newEnd, arith]
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using heapLenLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using globInv
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using genInv
  refine ⟨eoh, trig, curr, m1, ?_, ?_, currLookup, rfl, ?_, ?_⟩
  · simpa [eoh, Nat.add_assoc] using endLookup
  · simpa [trig] using triggerLookup
  · simpa [step, newEnd, aEq, Nat.add_assoc] using run
  · exact heapMem1

/-- HOL `memory_rel_AllocThunk`. The six source conjuncts are the single
hypothesis `valid`; HOL's `let w' = eoh − bytes_in_word * 2w` and
`w1 = trig − bytes_in_word * 2w` are inlined, `st |+ (EndOfHeap, _) |+
(TriggerGC, _)` is two `HolFiniteMapExact.update`s in that order, and the
independent HOL word type of `make_ptr`'s `0w` is the width `tagWidth`, as in
the reviewed `memory_rel_Ref`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_AllocThunk"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_allocThunk {width : Nat} {tagWidth : Nat} [NeZero width] [NeZero tagWidth]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (v : Flapjack.Compiler.Backend.DataSem.Value) (w : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (ev : AstHOL.ThunkMode)
    (hd : BitVec width) (new : Nat)
    (valid : memoryRel c be ts refs sp st m dm ((v, w) :: vars) ∧
      DataToWord.encodeHeader c (match ev with | .evaluated => 14 | .notEvaluated => 6) 1 = some hd ∧
      ¬ sptDomain refs new ∧ (ev = .evaluated → destThunk v refs = .notThunk) ∧ 2 ≤ sp ∧ goodDimindex width) :
    ∃ eoh curr trig : BitVec width, ∃ m1, st.lookup .endOfHeap = some (.word eoh) ∧
      st.lookup .triggerGC = some (.word trig) ∧ st.lookup .currHeap = some (.word curr) ∧
      storeList (eoh - wordSemBytesInWord * 2) [.word hd, w] m dm = some m1 ∧
      memoryRel c be ts (sptInsert new (.thunk ev v) refs) (sp - 2)
        ((st.update (.endOfHeap, .word (eoh - wordSemBytesInWord * 2))).update
          (.triggerGC, .word (trig - wordSemBytesInWord * 2))) m1 dm
        ((.refPtr false new, Build.makePtr c ((eoh - wordSemBytesInWord * 2) - curr) (0 : BitVec tagWidth) 1) :: vars) := by
  obtain ⟨rel, encoded, fresh, evaluated, enough, good⟩ := valid
  obtain ⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩ := rel
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  have absInv1 : absMlInv c (v :: vars.map Prod.fst) refs (roots, heap, be, a, sp0, sp1, gens) limit ts := by
    simpa using absInv
  obtain ⟨r, roots2, heap2, rootsEq, stored, absAfter⟩ :=
    newThunk c v (vars.map Prod.fst) refs roots heap be a sp0 sp1 gens limit ts new ev
      ⟨absInv1, fresh, by omega, evaluated⟩
  subst rootsEq
  cases addresses with
  | cons rAddr tailAddr =>
  have wordEq : wordAddr c r = w := rAddr
  obtain ⟨eoh, trig, curr, m1, endLookup, triggerLookup, currLookup, eohEq, run, heapMem1⟩ :=
    heapInMemoryStore_allocateThunk c ev heap heap2 a sp0 sp1 gens st m dm limit r hd encoded good
      absInv1.2.2.2.1 (by omega) stored heapMem
  have two : (2 : BitVec width) = BitVec.ofNat width 2 := rfl
  let offset := a + sp0 + sp1 - 2
  have absPopped : absMlInv c (.refPtr false new :: vars.map Prod.fst) (sptInsert new (.thunk ev v) refs)
      (.pointer offset (.word 0) :: roots2, heap2, be, a, sp0 - 2, sp1, gens) limit ts := by
    apply popThm c [v] (.refPtr false new :: vars.map Prod.fst) _ [r] _ heap2 be a (sp0 - 2) sp1 gens limit ts
    exact ⟨by simpa [offset] using absAfter, rfl⟩
  have ptrEq : wordAddr c (.pointer offset (.word 0)) =
      Build.makePtr c ((eoh - wordSemBytesInWord * BitVec.ofNat width 2) - curr) (0 : BitVec tagWidth) 1 := by
    have stride : StackRemove.bytesInWord width * BitVec.ofNat width offset =
        (BitVec.ofNat width offset <<< wordShiftAmount width) := by
      rcases good with h | h <;> subst width <;> apply BitVec.eq_of_toNat_eq <;>
        simp [StackRemove.bytesInWord, wordShiftAmount, BitVec.toNat_mul,
          BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_mod]
    have boundary : a + sp0 + sp1 = offset + 2 := by dsimp [offset]; omega
    have delta : (eoh - wordSemBytesInWord * BitVec.ofNat width 2) - curr =
        StackRemove.bytesInWord width * BitVec.ofNat width offset := by
      rw [eohEq, boundary]
      simp [wordSemBytesInWord, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add, ← BitVec.add_assoc]
    have shifts : wordShiftAmount width + (shiftLength c - wordShiftAmount width) = shiftLength c := by
      have h := heapMem.2.2.1
      omega
    simp only [Build.makePtr, delta, stride, ← BitVec.shiftLeft_add, shifts, wordAddr, getAddr, getLowerBits]
    simp
  refine ⟨eoh, curr, trig, m1, endLookup, triggerLookup, currLookup, ?_, ?_⟩
  · rw [two, ← wordEq]
    exact run
  · rw [two]
    refine ⟨heap2, limit, a, sp0 - 2, sp1, gens, heapMem1, ?_, limitBound, by omega⟩
    refine ⟨.pointer offset (.word 0) :: roots2, absPopped, ?_⟩
    exact List.Forall₂.cons ptrEq tailAddr

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateRefs
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ArrayUpdateValue
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Preliminaries
public import Flapjack.HolArb
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateValue
public import Flapjack.Compiler.Backend.GcShared.HeapSimilarity

@[expose] public section

/-!
# Reference updates: edges, reachability and reference-block heap lookups

Counterparts of `ref_edge_ValueArray`, `ref_edge_Thunk`,
`reachable_refs_UPDATE`, `reachable_refs_Thunk_UPDATE`,
`reachable_refs_UPDATE1`, `v_inv_ByteArray_insert_lemma`, `heap_lookup_RefBlock_lemma`,
`heap_store_RefBlock`, `NOT_isRefBlock`, `v_inv_Ref_lemma`, `v_inv_Ref` and
`v_inv_ValueArray_insert_lemma` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. The
`ARB` tag of the temporary `Block 0 ARB xs` is the reviewed `holArb`, and
`ptr ∈ domain refs` is `sptMem ptr refs`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- HOL `ref_edge_ValueArray`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ref_edge_ValueArray"]
theorem refEdge_valueArray (ptr : Nat) (xs : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x y : Nat) :
    refEdge (sptInsert ptr (.valueArray xs) refs) x y ↔
      if x = ptr then y ∈ getRefs (.block 0 (holArb Nat) xs) else refEdge refs x y := by
  by_cases h : x = ptr
  · subst h
    simp [refEdge, sptLookup_sptInsert_same, getRefs]
  · simp [refEdge, sptLookup_sptInsert_ne ptr x _ refs h, h]

/-- HOL `ref_edge_Thunk`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "ref_edge_Thunk"]
theorem refEdge_thunk (ptr : Nat) (ev : AstHOL.ThunkMode) (v : Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x y : Nat) :
    refEdge (sptInsert ptr (.thunk ev v) refs) x y ↔
      if x = ptr then y ∈ getRefs (.block 0 (holArb Nat) [v]) else refEdge refs x y := by
  by_cases h : x = ptr
  · subst h
    simp [refEdge, sptLookup_sptInsert_same, getRefs]
  · simp [refEdge, sptLookup_sptInsert_ne ptr x _ refs h, h]

/-- Replacing one reference cell does not add reachable references when
every edge out of the new cell leads to a reference already reachable. -/
theorem reachableRefs_insert_subset (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (roots : List Flapjack.Compiler.Backend.DataSem.Value) (ptr : Nat)
    (cell : BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)
    (fresh : ∀ dest, refEdge (sptInsert ptr cell refs) ptr dest → reachableRefs roots refs dest)
    (target : Nat) :
    reachableRefs roots (sptInsert ptr cell refs) target → reachableRefs roots refs target := by
  have step : ∀ source dest, reachableRefs roots refs source →
      refEdge (sptInsert ptr cell refs) source dest → reachableRefs roots refs dest := by
    intro source dest reachable edge
    by_cases same : source = ptr
    · subst source
      exact fresh dest edge
    · have oldEdge : refEdge refs source dest := by
        simpa [refEdge, sptLookup_sptInsert_ne ptr source _ refs same] using edge
      obtain ⟨root, start, member, reference, path⟩ := reachable
      exact ⟨root, start, member, reference, path.tail oldEdge⟩
  rintro ⟨root, start, rootMember, reference, path⟩
  have startReach : reachableRefs roots refs start := ⟨root, start, rootMember, reference, .refl⟩
  induction path with
  | refl => exact startReach
  | tail path edge ih => exact step _ _ ih edge

/-- HOL `reachable_refs_UPDATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_UPDATE"]
theorem reachableRefs_update (xs stack : List Flapjack.Compiler.Backend.DataSem.Value) (b : Bool)
    (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (n : Nat) :
    reachableRefs (xs ++ .refPtr b ptr :: stack) (sptInsert ptr (.valueArray xs) refs) n →
      reachableRefs (xs ++ .refPtr b ptr :: stack) refs n :=
  reachableRefs_updateValueArray refs xs stack ptr b n

/-- HOL `reachable_refs_Thunk_UPDATE`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_Thunk_UPDATE"]
theorem reachableRefs_thunkUpdate (v : Flapjack.Compiler.Backend.DataSem.Value) (b : Bool) (ptr : Nat)
    (stack : List Flapjack.Compiler.Backend.DataSem.Value) (ev : AstHOL.ThunkMode)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (n : Nat) :
    reachableRefs (v :: .refPtr b ptr :: stack) (sptInsert ptr (.thunk ev v) refs) n →
      reachableRefs (v :: .refPtr b ptr :: stack) refs n := by
  apply reachableRefs_insert_subset
  intro dest edge
  rw [refEdge_thunk, if_pos rfl] at edge
  simp only [getRefs, List.flatMap_cons, List.flatMap_nil, List.append_nil] at edge
  exact ⟨v, dest, by simp, edge, .refl⟩

/-- HOL `reachable_refs_UPDATE1`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "reachable_refs_UPDATE1"]
theorem reachableRefs_update1 (xs stack xs1 : List Flapjack.Compiler.Backend.DataSem.Value) (b : Bool)
    (ptr : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (n : Nat) :
    reachableRefs (xs ++ .refPtr b ptr :: stack) (sptInsert ptr (.valueArray xs1) refs) n →
      (∀ v, v ∈ xs1 → v ∉ xs → ∃ xs2, sptLookup ptr refs = some (.valueArray xs2) ∧ v ∈ xs2) →
      reachableRefs (xs ++ .refPtr b ptr :: stack) refs n := by
  intro reach origin
  apply reachableRefs_insertValueArray_subset refs _ xs1 ptr b (by simp) _ n reach
  intro v member
  by_cases inXs : v ∈ xs
  · exact Or.inl (List.mem_append_left _ inXs)
  · exact Or.inr (origin v member inXs)

/-- HOL `heap_lookup_RefBlock_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_lookup_RefBlock_lemma"]
theorem heapLookup_refBlock_lemma {α β : Type} (n : Nat) (ha hb : List (HeapElement α (HeapTag × List β)))
    (y : List (HeapAddress α)) (x : HeapElement α (HeapTag × List β)) :
    (heapLookup n (ha ++ refBlock y :: hb) = some x) ↔
      if n < heapLength ha then heapLookup n ha = some x
      else if n = heapLength ha then x = refBlock y
      else if heapLength ha + (y.length + 1) ≤ n then
        heapLookup (n - heapLength ha - (y.length + 1)) hb = some x
      else False := by
  rw [heapLookup_append]
  by_cases lt : n < heapLength ha
  · simp [lt]
  · simp only [lt, if_false]
    by_cases eq : n = heapLength ha
    · subst eq
      simp [heapLookup, eq_comm]
    · have pos : n - heapLength ha ≠ 0 := by omega
      simp only [eq, if_false, heapLookup, pos, refBlock, elLength]
      by_cases le : heapLength ha + (y.length + 1) ≤ n
      · have notLt : ¬ n - heapLength ha < y.length + 1 := by omega
        simp only [notLt, if_false, le, if_true]
      · have isLt : n - heapLength ha < y.length + 1 := by omega
        simp [isLt, le]

/-- HOL `NOT_isRefBlock`; every conjunct keeps its own carriers. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "NOT_isRefBlock"
  (words_as_type_indexed_bitvec)]
theorem not_isRefBlock {wa : Nat} {wb : Nat} [NeZero wa] [NeZero wb] {α η γ δ : Type}
    (x : Int) (w : BitVec 64) (xs : List (HeapAddress γ)) (n : Nat) :
    ¬ isRefBlock (bignumRep x : HeapElement α (HeapTag × List (WordLocW wa))) ∧
      ¬ isRefBlock (word64Rep w : HeapElement η (HeapTag × List (WordLocW wb))) ∧
      ¬ isRefBlock (HeapElement.dataElement xs xs.length (HeapTag.blockTag n, ([] : List δ))) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨pointers, h⟩
    simp [bignumRep, refBlock] at h
  · rintro ⟨pointers, h⟩
    unfold word64Rep at h
    split at h <;> simp [refBlock] at h
  · rintro ⟨pointers, h⟩
    simp [refBlock] at h

/-- HOL `v_inv_ByteArray_insert_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_ByteArray_insert_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_insertByteArray_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (ptr : Nat) (fl : Bool) (xs : List (BitVec 8)) :
    ∀ (ck : Nat) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (y : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      valueInv conf v1 refs (y, f, tf, heap) ∧
        (sptMem ptr refs → ∃ a b, sptLookup ptr refs = some (.byteArray a b)) →
      ClockValueInv ck conf v1 (sptInsert ptr (.byteArray fl xs) refs) (y, f, tf, heap) := by
  rintro ck v1 refs y f tf heap ⟨inv, domain⟩
  have all := valueInv_insertByteArray conf v1 refs y f tf heap ptr fl xs ⟨inv, domain⟩
  exact all ck

/-- HOL `v_inv_ValueArray_insert_lemma`; the free `heap2` only occurs in the
`RefBlock_inv` premise, as in HOL. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_ValueArray_insert_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_insertValueArray_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (ptr : Nat)
    (xs : List Flapjack.Compiler.Backend.DataSem.Value) :
    ∀ (ck : Nat) (v1 : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (y : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      valueInv conf v1 refs (y, f, tf, heap) ∧ refBlockInv heap heap2 ∧
        (sptMem ptr refs → ∃ as, sptLookup ptr refs = some (.valueArray as)) →
      ClockValueInv ck conf v1 (sptInsert ptr (.valueArray xs) refs) (y, f, tf, heap) := by
  rintro ck v1 refs y f tf heap ⟨inv, -, domain⟩
  have all := valueInv_insertValueArray conf v1 refs y f tf heap ptr xs heap ⟨⟨fun _ _ h => h.1, fun _ _ h => h.1⟩, inv, domain⟩
  exact all ck

/-- HOL `v_inv_Ref_lemma`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_Ref_lemma"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_ref_lemma {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) :
    ∀ (ck : Nat) (w : Flapjack.Compiler.Backend.DataSem.Value)
      (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (x : HeapAddress (WordLocW width))
      (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
      (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))),
      valueInv conf w refs (x, f, tf, heap) ∧ refBlockInv heap heap2 →
      (ClockValueInv ck conf w refs (x, f, tf, heap) ↔ ClockValueInv ck conf w refs (x, f, tf, heap2)) := by
  rintro ck w refs x f tf heap ⟨-, inv⟩
  exact ⟨clockValueInv_refBlockHeap ck conf refs f tf heap heap2 inv w x,
    clockValueInv_refBlockHeap ck conf refs f tf heap2 heap ⟨inv.2, inv.1⟩ w x⟩

/-- HOL `v_inv_Ref`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_Ref"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_ref {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (heap heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) :
    refBlockInv heap heap2 →
      ∀ (x : Flapjack.Compiler.Backend.DataSem.Value) (h : HeapAddress (WordLocW width))
        (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat),
        (valueInv conf x refs (h, f, tf, heap2) ↔ valueInv conf x refs (h, f, tf, heap)) := by
  intro inv x h f tf
  exact ⟨fun v ck => clockValueInv_refBlockHeap ck conf refs f tf heap2 heap ⟨inv.2, inv.1⟩ x h (v ck),
    fun v ck => clockValueInv_refBlockHeap ck conf refs f tf heap heap2 inv x h (v ck)⟩

/-- Replacing the head of a heap by an element of the same length changes
only the lookup at offset zero. -/
theorem heapLookup_cons_sameLength {α β : Type} (X Y : HeapElement α β) (suf : List (HeapElement α β))
    (len : elLength X = elLength Y) (k : Nat) :
    heapLookup k (X :: suf) = if k = 0 then some X else heapLookup k (Y :: suf) := by
  by_cases z : k = 0
  · simp [z, heapLookup]
  · simp [z, heapLookup, len]

/-- HOL `heap_store_RefBlock`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_store_RefBlock"]
theorem heapStore_refBlock_source {α β : Type} (y h : List (HeapAddress α)) (n : Nat)
    (heap : List (HeapElement α (HeapTag × List β))) :
    y.length = h.length ∧ heapLookup n heap = some (refBlock y) →
      ∃ heap2, heapStore n [refBlock h] heap = (heap2, true) ∧ refBlockInv heap heap2 ∧
        heapLookup n heap2 = some (refBlock h) ∧ heapLength heap2 = heapLength heap ∧
        heap2.filter isForwardPointer = heap.filter isForwardPointer ∧
        (∀ xs l d, HeapElement.dataElement xs l d ∈ heap2 →
          HeapElement.dataElement xs l d = refBlock h ∨ HeapElement.dataElement xs l d ∈ heap) ∧
        (∀ a, isSomeDataElement (heapLookup a heap2) ↔ isSomeDataElement (heapLookup a heap)) ∧
        ∀ m x, m ≠ n ∧ heapLookup m heap = some x → heapLookup m heap2 = some x := by
  rintro ⟨len, found⟩
  obtain ⟨pre, suf, rfl, rfl⟩ := heapLookup_split heap n _ found
  have elLen : elLength (refBlock h : HeapElement α (HeapTag × List β)) =
      elLength (refBlock y : HeapElement α (HeapTag × List β)) := by
    simp [refBlock, elLength, len]
  have lookup : ∀ a, heapLookup a (pre ++ refBlock h :: suf) =
      if a = heapLength pre then some (refBlock h) else heapLookup a (pre ++ refBlock y :: suf) := by
    intro a
    rw [heapLookup_append, heapLookup_append]
    by_cases lt : a < heapLength pre
    · simp [lt, show a ≠ heapLength pre by omega]
    · simp only [lt, if_false]
      rw [heapLookup_cons_sameLength _ _ suf elLen]
      by_cases eq : a = heapLength pre
      · simp [eq]
      · simp [eq, show a - heapLength pre ≠ 0 by omega]
  refine ⟨pre ++ refBlock h :: suf, heapStore_refBlock pre suf h y len.symm, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · rintro m x ⟨hm, notRef⟩
      rw [lookup]
      by_cases eq : m = heapLength pre
      · subst eq
        rw [heapLookup_prefix] at hm
        cases hm
        exact absurd ⟨y, rfl⟩ notRef
      · simp [eq, hm]
    · rintro m x ⟨hm, notRef⟩
      rw [lookup] at hm
      by_cases eq : m = heapLength pre
      · simp only [eq, if_true, Option.some.injEq] at hm
        subst hm
        exact absurd ⟨h, rfl⟩ notRef
      · simpa [eq] using hm
  · exact heapLookup_prefix pre suf _
  · simp [heapLength, elLength, refBlock, len]
  · simp [List.filter_append, isForwardPointer, refBlock]
  · intro xs l d member
    simp only [List.mem_append, List.mem_cons] at member
    rcases member with member | eq | member
    · exact Or.inr (by simp [member])
    · exact Or.inl eq
    · exact Or.inr (by simp [member])
  · intro a
    rw [lookup]
    by_cases eq : a = heapLength pre
    · subst eq
      rw [heapLookup_prefix]
      simp [isSomeDataElement, refBlock]
    · simp [eq]
  · rintro m x ⟨ne, hm⟩
    rw [lookup, if_neg ne]
    exact hm

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

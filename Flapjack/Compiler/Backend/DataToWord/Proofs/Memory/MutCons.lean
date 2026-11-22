module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.FinaliseCons
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConsMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshBlockGc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshBlockRef

@[expose] public section

/-!
# Allocating mutable constructor cells

Counterparts of `v_inv_MutCons_step`, `mutcons_thm_alt`, `mutcons_thm` and
`memory_rel_MutCons` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`.
`k IN domain refs` is `sptMem k refs`, `FDOM f SUBSET domain refs` is
`∀ k, f.lookup k ≠ none → sptMem k refs`, `f |+ (ptr,a)` is
`f.updateEq (ptr, a)`, `TAKE`/`DROP` are `List.take`/`List.drop` and `EL` is
`holEl`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- HOL `v_inv_MutCons_step`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "v_inv_MutCons_step"
  (fmap_as_finite_support_relation := [f, tf]) (words_as_type_indexed_bitvec)]
theorem valueInv_mutConsStep {width : Nat} [NeZero width]
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (v : Flapjack.Compiler.Backend.DataSem.Value) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (y : HeapAddress (WordLocW width)) (f : HolFiniteMapExact Nat Nat) (tf : HolFiniteMapExact Nat Nat)
    (heap : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (ptr : Nat)
    (heap2 : List (HeapElement (WordLocW width) (HeapTag × List (WordLocW width)))) (tag : Nat)
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value) (r : List Flapjack.Compiler.Backend.DataSem.Value) (a : Nat) :
    valueInv conf v refs (y, f, tf, heap) ∧ ¬ sptMem ptr refs ∧
        (∀ k, f.lookup k ≠ none → sptMem k refs) ∧ heapStoreRel heap heap2 →
      valueInv conf v (sptInsert ptr (.mutBlock tag false l c r) refs) (y, f.updateEq (ptr, a), tf, heap2) := by
  rintro ⟨inv, fresh, sub, rel⟩
  have notIn : f.lookup ptr = none := by
    cases h : f.lookup ptr with
    | none => rfl
    | some v => exact absurd (sub ptr (by simp [h])) fresh
  have ins := valueInv_insertMutBlock conf v refs y f tf heap ptr tag false l c r ⟨inv, fresh, sub⟩
  apply valueInv_submap conf _ f (f.updateEq (ptr, a)) tf tf heap heap2 v y
  refine ⟨?_, HolFiniteMapExact.submap_refl tf, rel, ins⟩
  intro k val h
  have ne : k ≠ ptr := by rintro rfl; simp [notIn] at h
  simp [HolFiniteMapExact.updateEq, FUPDATE_HOL, ne, h]

/-- The stack/reference invariant after a mutable constructor cell replaces an
unused heap region: the fields on the stack prefix move into a fresh
`MutBlock` reference at `ptr`, which `f` maps to the new heap cell. Flapjack
proof infrastructure for `mutcons_thm_alt`. -/
theorem bcStackRefInv_mutcons {width : Nat} [NeZero width] (conf : Flapjack.Compiler.Backend.DataToWord.Config)
    (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value) (r stack : List Flapjack.Compiler.Backend.DataSem.Value) (rs roots : List (HeapAddress (WordLocW width)))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (pre post remainder : ValueHeap width) (unused ts tag ptr : Nat)
    (be : Bool) (lengths : rs.length = (l ++ [c] ++ r).length)
    (size : heapLength (blockRep tag rs :: remainder) = unused + 1)
    (fresh : ¬ sptMem ptr refs) (gc : ∀ gs, conf.gcKind ≠ .generational gs)
    (inv : bcStackRefInv conf ts (l ++ [c] ++ r ++ stack) refs
      (rs ++ roots, pre ++ [.unused unused] ++ post, be)) :
    bcStackRefInv conf ts (.refPtr false ptr :: stack) (sptInsert ptr (.mutBlock tag false l c r) refs)
      (.pointer (heapLength pre) (.word (ptrBits conf tag (l ++ [c] ++ r).length)) :: roots,
       pre ++ (blockRep tag rs :: remainder) ++ post, be) := by
  obtain ⟨f, tf, fInj, fDomain, tfInj, tfTimes, tfBound, endian, unique, values, refInv⟩ := inv
  set oldHeap : ValueHeap width := pre ++ [.unused unused] ++ post with hOld
  set newHeap : ValueHeap width := pre ++ (blockRep tag rs :: remainder) ++ post with hNew
  set a := heapLength pre with ha
  set f' := f.updateEq (ptr, a) with hf'
  set refs' := sptInsert ptr (.mutBlock tag false l c r) refs with hrefs'
  have preserved : ∀ p cell, isDataElement cell → heapLookup p oldHeap = some cell →
      heapLookup p newHeap = some cell :=
    fun p cell d h => heapLookup_allocate_preservesData pre post (blockRep tag rs :: remainder) unused size p cell d h
  have dataPreserved : ∀ p, isSomeDataElement (heapLookup p oldHeap) →
      isSomeDataElement (heapLookup p newHeap) := by
    rintro p ⟨xs, len, d, h⟩
    exact ⟨xs, len, d, preserved p _ (by simp [isDataElement]) h⟩
  have rel : heapStoreRel oldHeap newHeap := by
    rintro p ⟨xs, len, d, h⟩
    rw [h]; exact preserved p _ (by simp [isDataElement]) h
  have newCell : heapLookup a newHeap = some (blockRep tag rs) := by
    have found := Flapjack.Compiler.Backend.heapLookup_prefix pre (remainder ++ post) (blockRep tag rs)
    simpa [newHeap, List.append_assoc, List.cons_append] using found
  have newData : isSomeDataElement (heapLookup a newHeap) := by
    rw [newCell]; simp [isSomeDataElement, blockRep]
  have sub : ∀ k, f.lookup k ≠ none → sptMem k refs := by
    intro k h
    obtain ⟨cell, hc⟩ := fDomain k (by cases e : f.lookup k with
      | none => exact absurd e h
      | some v => exact ⟨v, e⟩)
    simp [sptMem, sptDomain, hc]
  have fNone : f.lookup ptr = none := by
    cases h : f.lookup ptr with
    | none => rfl
    | some v => exact absurd (sub ptr (by simp [h])) fresh
  have absent : sptLookup ptr refs = none := by
    cases h : sptLookup ptr refs with
    | none => rfl
    | some cell => exact absurd (by simp [sptMem, sptDomain, h]) fresh
  have f'Lookup : ∀ k, f'.lookup k = if k = ptr then some a else f.lookup k := by
    intro k; simp [hf', HolFiniteMapExact.updateEq, FUPDATE_HOL]
  have refsLookup : ∀ k, sptLookup k refs' = if k = ptr then some (.mutBlock tag false l c r) else sptLookup k refs := by
    intro k
    by_cases h : k = ptr
    · subst h; simp [hrefs', sptLookup_sptInsert_same]
    · simp [hrefs', sptLookup_sptInsert_ne _ _ _ _ h, h]
  have fFresh := mapInjInto_unused_fresh f pre post unused fInj
  have tfFresh := mapInjInto_unused_fresh tf pre post unused tfInj
  have step : ∀ v y, valueInv conf v refs (y, f, tf, oldHeap) → valueInv conf v refs' (y, f', tf, newHeap) :=
    fun v y h => valueInv_mutConsStep conf v refs y f tf oldHeap ptr newHeap tag l c r a ⟨h, fresh, sub, rel⟩
  have fieldRel : List.Forall₂ (fun value address => valueInv conf value refs (address, f, tf, oldHeap))
      (l ++ [c] ++ r) rs := by
    have := List.forall₂_take (l ++ [c] ++ r).length values
    have h2 : (rs ++ roots).take (l ++ [c] ++ r).length = rs := by rw [← lengths]; exact List.take_left
    rwa [List.take_left, h2] at this
  have stackRel : List.Forall₂ (fun value address => valueInv conf value refs (address, f, tf, oldHeap))
      stack roots := by
    have := List.forall₂_drop (l ++ [c] ++ r).length values
    have h2 : (rs ++ roots).drop (l ++ [c] ++ r).length = roots := by rw [← lengths]; exact List.drop_left
    rwa [List.drop_left, h2] at this
  have fApply : ∀ k, k ≠ ptr → holFapply f' k = holFapply f k := by
    intro k hk; simp [holFapply, f'Lookup, hk]
  have fApplyPtr : holFapply f' ptr = a := holFapply_of_lookup (by simp [f'Lookup])
  refine ⟨f', tf, ?_, ?_, ⟨fun k d => dataPreserved _ (tfInj.1 k d), tfInj.2⟩,
    fun n hn => allTimestamps_mutcons ptr tag refs l c r stack fresh n (tfTimes n hn), tfBound, endian,
    blocksUnique_mutcons ts ptr tag refs l c r stack unique, ?_, ?_⟩
  · constructor
    · rintro k ⟨v, hv⟩
      by_cases hk : k = ptr
      · subst hk; rw [fApplyPtr]; exact newData
      · rw [fApply k hk]
        rw [f'Lookup, if_neg hk] at hv
        exact dataPreserved _ (fInj.1 k ⟨v, hv⟩)
    · rintro x y ⟨⟨vx, hx⟩, ⟨vy, hy⟩⟩ eq
      rw [f'Lookup] at hx hy
      by_cases ex : x = ptr <;> by_cases ey : y = ptr
      · rw [ex, ey]
      · rw [ex, fApplyPtr, fApply y ey] at eq
        rw [if_neg ey] at hy
        exact absurd eq.symm (fFresh y ⟨vy, hy⟩)
      · rw [ey, fApplyPtr, fApply x ex] at eq
        rw [if_neg ex] at hx
        exact absurd eq (fFresh x ⟨vx, hx⟩)
      · rw [fApply x ex, fApply y ey] at eq
        rw [if_neg ex] at hx; rw [if_neg ey] at hy
        exact fInj.2 x y ⟨⟨vx, hx⟩, ⟨vy, hy⟩⟩ eq
  · rintro n ⟨v, hv⟩
    rw [refsLookup]
    rw [f'Lookup] at hv
    split
    · exact ⟨_, rfl⟩
    · rename_i hn; rw [if_neg hn] at hv; exact fDomain n ⟨v, hv⟩
  · refine List.Forall₂.cons ?_ (stackRel.imp fun v y h => step v y h)
    have noThunk : ∀ mode value, sptLookup ptr refs' ≠ some (.thunk mode value) := by
      intro mode value h; rw [refsLookup, if_pos rfl] at h; cases h
    apply (valueInv_refPtr_notThunk conf false ptr refs' _ f' tf newHeap noThunk).mpr
    refine ⟨⟨a, by simp [f'Lookup]⟩, fun _ _ _ _ _ _ => rfl, ?_⟩
    rw [fApplyPtr, refsLookup, if_pos rfl]
    simp only [refPtrAnnot, List.length_append, List.length_singleton]
  · rintro n ⟨reach, ⟨fn, hfn⟩⟩
    by_cases hn : n = ptr
    · subst hn
      simp only [bcRefInv, hfn, refsLookup]
      rw [f'Lookup, if_pos rfl] at hfn
      cases hfn
      refine ⟨gc, ?_, rs, newCell, (fieldRel.flip).imp fun y v h => step v y h⟩
      rintro - ⟨stamp, dom, eq⟩
      exact tfFresh stamp dom eq
    · rw [f'Lookup, if_neg hn] at hfn
      have oldReach := reachableRefs_mutCons ptr tag n stack l c r refs ⟨reach, hn, fresh⟩
      have old := refInv n ⟨oldReach, ⟨fn, hfn⟩⟩
      have fnNe : fn ≠ a := by
        have := fFresh n ⟨fn, hfn⟩
        rwa [holFapply_of_lookup hfn] at this
      simp only [bcRefInv, hfn] at old
      simp only [bcRefInv, f'Lookup, if_neg hn, hfn, refsLookup]
      revert old
      cases hcell : sptLookup n refs with
      | none => simp
      | some cell =>
        cases cell with
        | valueArray values =>
          rintro ⟨addrs, h1, h2⟩
          exact ⟨addrs, preserved _ _ (by simp [isDataElement, refBlock]) h1, h2.imp fun y v h => step v y h⟩
        | byteArray cmp bytes =>
          intro h1
          exact preserved _ _ (by simp [isDataElement, bytesRep]) h1
        | thunk mode value =>
          rintro ⟨addr, h1, h2, h3⟩
          refine ⟨addr, preserved _ _ (by simp [isDataElement, thunkBlock]) h1, ?_, step _ _ h3⟩
          intro ev
          exact destThunk_insert_fresh ptr refs value _ ⟨fresh, h2 ev⟩
        | mutBlock tag' fin' l' c' r' =>
          rintro ⟨g, ns, addrs, h1, h2⟩
          exact ⟨g, ns, addrs, preserved _ _ (by simp [isDataElement, blockRep]) h1,
            h2.imp fun y v h => step v y h⟩

/-- HOL `mutcons_thm_alt`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "mutcons_thm_alt"
  (words_as_type_indexed_bitvec)]
theorem mutconsThm_alt {width : Nat} [NeZero width] {β γ : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (l : List Flapjack.Compiler.Backend.DataSem.Value) (c : Flapjack.Compiler.Backend.DataSem.Value) (r stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit ts ptr tag : Nat) :
    absMlInv conf (l ++ [c] ++ r ++ stack) refs (roots, heap, be, a, sp, sp1, gens) limit ts ∧
        (l ++ [c] ++ r).length < sp ∧ ¬ sptMem ptr refs ∧ (∀ gs, conf.gcKind ≠ .generational gs) →
      ∃ rs roots2 heap2, roots = rs ++ roots2 ∧ rs.length = (l ++ [c] ++ r).length ∧
        heapStoreUnusedAlt a (sp + sp1) (blockRep tag rs) heap = (heap2, true) ∧
        absMlInv conf (.refPtr false ptr :: stack) (sptInsert ptr (.mutBlock tag false l c r) refs)
          (.pointer a (.word (ptrBits conf tag (l ++ [c] ++ r).length : BitVec width)) :: roots2,
           heap2, be, a + elLength (blockRep (β := β) tag rs), sp - elLength (blockRep (β := γ) tag rs),
           sp1, gens) limit ts := by
  rintro ⟨inv, enough, fresh, gc⟩
  obtain ⟨rs, roots2, rootEq, rootLen⟩ :=
    split1Thm conf (l ++ [c] ++ r) stack refs roots heap be a sp sp1 gens limit ts inv
  have sizeAny (δ : Type) : elLength (blockRep (β := δ) tag rs) = rs.length + 1 := by simp [blockRep, elLength]
  have fit : elLength (blockRep (β := WordLocW width) tag rs) ≤ sp + sp1 := by
    rw [sizeAny, rootLen]; omega
  obtain ⟨heap2, stored, -⟩ := heapStoreUnusedAlt_exists a (sp + sp1) heap (blockRep tag rs) inv.2.2.2.1 fit
  have positive : sp + sp1 ≠ 0 := by omega
  have found := inv.2.2.2.1.1 positive
  obtain ⟨pre, post, shape, aEq⟩ := heapLookup_split heap a _ found
  have expand : (heapExpand (sp + sp1) : ValueHeap width) = [.unused (sp + sp1 - 1)] := by
    unfold heapExpand
    rw [if_neg positive]
  let newHeap : ValueHeap width := pre ++ [blockRep tag rs] ++ heapExpand (sp + sp1 - (rs.length + 1)) ++ post
  have heapEq : heap2 = newHeap := by
    unfold heapStoreUnusedAlt at stored
    classical
    simp only [found, fit, and_self, ↓reduceIte] at stored
    rw [shape, aEq, heapStore_atPrefix] at stored
    have eq := congrArg Prod.fst stored
    simpa [newHeap, sizeAny, List.append_assoc] using eq.symm
  refine ⟨rs, roots2, heap2, rootEq, rootLen, stored, ?_⟩
  obtain ⟨rootsValid, heapValid, gcValid, unusedValid, stackValid⟩ := inv
  have oldHeap : heap = pre ++ heapExpand (sp + sp1) ++ post := by
    simpa [expand, List.append_assoc] using shape
  rw [oldHeap] at rootsValid heapValid gcValid unusedValid
  rw [aEq] at gcValid unusedValid
  have preData : ∀ element ∈ pre, isDataElement element :=
    dataUpTo_prefix_data pre (heapExpand (sp + sp1) ++ post) (by simpa [List.append_assoc] using unusedValid.2.2)
  have heapResult := heapOk_allocateBlock pre post (rs ++ roots2) rs (sp + sp1) tag limit
    (.word (ptrBits conf tag (l ++ [c] ++ r).length)) (by omega) (by rw [← rootEq]; exact rootsValid)
    heapValid (by intro address member; exact List.mem_append_left _ member)
  have gcResult := gcKindInv_allocateData conf pre post rs ([] : List (WordLocW width))
    (.blockTag tag) sp sp1 rs.length gens (by simp [isMutTag]) (by omega) gcValid
  have unusedResult := unusedSpaceInv_allocateData pre post rs rs.length (sp + sp1) (.blockTag tag, ([] : List (WordLocW width))) preData
  have remainingEq : (sp + sp1) - (rs.length + 1) = (sp - (rs.length + 1)) + sp1 := by omega
  have size : heapLength (blockRep (β := WordLocW width) tag rs :: heapExpand ((sp + sp1) - (rs.length + 1))) =
      (sp + sp1 - 1) + 1 := by
    change heapLength ([blockRep tag rs] ++ heapExpand ((sp + sp1) - (rs.length + 1))) = _
    rw [heapLength_append, heapLength_heapExpand]
    have one : heapLength [blockRep (β := WordLocW width) tag rs] = rs.length + 1 := by
      simp [heapLength, blockRep, elLength]
    rw [one]
    omega
  have stackResult := bcStackRefInv_mutcons conf l c r stack rs roots2 refs pre post
    (heapExpand ((sp + sp1) - (rs.length + 1))) (sp + sp1 - 1) ts tag ptr be rootLen size fresh gc
    (by simpa only [oldHeap, expand, rootEq, List.append_assoc, List.singleton_append] using stackValid)
  rw [heapEq, sizeAny, sizeAny, aEq]
  refine ⟨?_, by simpa [newHeap, List.append_assoc] using heapResult.2, ?_, ?_, ?_⟩
  · intro p v member
    have := heapResult.1 p v (by
      rcases List.mem_cons.mp member with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ h))
    simpa [newHeap, List.append_assoc] using this
  · simpa [newHeap, blockRep, List.append_assoc] using gcResult
  · simpa [newHeap, remainingEq, blockRep, List.append_assoc] using unusedResult
  · simpa [newHeap, List.append_assoc] using stackResult

/-- HOL `mutcons_thm`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "mutcons_thm"
  (words_as_type_indexed_bitvec)]
theorem mutconsThm {width : Nat} [NeZero width] {β γ : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (xs stack : List Flapjack.Compiler.Backend.DataSem.Value)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (roots : List (HeapAddress (WordLocW width))) (heap : ValueHeap width)
    (be : Bool) (a sp sp1 : Nat) (gens : GenState) (limit ts index ptr tag : Nat) :
    absMlInv conf (xs ++ stack) refs (roots, heap, be, a, sp, sp1, gens) limit ts ∧
        xs.length < sp ∧ index < xs.length ∧ ¬ sptMem ptr refs ∧ (∀ gs, conf.gcKind ≠ .generational gs) →
      ∃ rs roots2 heap2, roots = rs ++ roots2 ∧ rs.length = xs.length ∧
        heapStoreUnusedAlt a (sp + sp1) (blockRep tag rs) heap = (heap2, true) ∧
        absMlInv conf (.refPtr false ptr :: stack)
          (sptInsert ptr (.mutBlock tag false (xs.take index) (holEl index xs) (xs.drop (index + 1))) refs)
          (.pointer a (.word (ptrBits conf tag xs.length : BitVec width)) :: roots2,
           heap2, be, a + elLength (blockRep (β := β) tag rs), sp - elLength (blockRep (β := γ) tag rs),
           sp1, gens) limit ts := by
  rintro ⟨inv, enough, index_lt, fresh, gc⟩
  have split := take_el_drop index xs index_lt
  rw [← split] at inv enough
  have := mutconsThm_alt (β := β) (γ := γ) conf (xs.take index) (holEl index xs) (xs.drop (index + 1)) stack refs
    roots heap be a sp sp1 gens limit ts ptr tag ⟨inv, enough, fresh, gc⟩
  rwa [split] at this

/-- HOL `memory_rel_MutCons`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_MutCons"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_mutCons {width : Nat} [NeZero width] (c : DataToWord.Config) (be : Bool)
    (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (vals : List Flapjack.Compiler.Backend.DataSem.Value) (ws : List (WordLocW width))
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (tag : Nat) (hd : BitVec width)
    (rel : memoryRel c be ts refs sp st m dm (vals.zip ws ++ vars))
    (lens : vals.length = ws.length) (_nonempty : vals ≠ [])
    (encoded : DataToWord.encodeHeader c (4 * tag) ws.length = some hd)
    (enough : ws.length < sp) (good : goodDimindex width) (index ptr : Nat)
    (indexLt : index < vals.length) (fresh : ¬ sptMem ptr refs)
    (gc : ∀ gs, c.gcKind ≠ .generational gs) :
    ∃ free curr m1, st.lookup .nextFree = some (.word free) ∧ st.lookup .currHeap = some (.word curr) ∧
      storeList free (.word hd :: ws) m dm = some m1 ∧
      memoryRel c be ts
        (sptInsert ptr (.mutBlock tag false (vals.take index) (holEl index vals) (vals.drop (index + 1))) refs) (sp - (ws.length + 1))
        (st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)))) m1 dm
        ((.refPtr false ptr, Build.makeConsPtr c (free - curr) tag ws.length) :: vars) := by
  obtain ⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩ := rel
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  have absInv1 : absMlInv c (vals ++ vars.map Prod.fst) refs
      (roots, heap, be, a, sp0, sp1, gens) limit ts := by
    simpa [List.map_append, List.map_fst_zip (Nat.le_of_eq lens)] using absInv
  obtain ⟨rs, roots2, heap2, rootsEq, rootsLen, stored, absAfter⟩ :=
    mutconsThm (β := WordLocW width) (γ := WordLocW width) c vals (vars.map Prod.fst) refs roots heap be a sp0 sp1 gens limit ts index ptr tag
      ⟨absInv1, by omega, indexLt, fresh, gc⟩
  have addrMap : roots.map (wordAddr c) = ws ++ vars.map Prod.snd := by
    have h := (every2_function_eq roots ((vals.zip ws ++ vars).map Prod.snd) (wordAddr c)).mp addresses
    simpa [List.map_append, List.map_snd_zip (Nat.le_of_eq lens.symm)] using h
  rw [rootsEq, List.map_append] at addrMap
  have ⟨mapped, tailMap⟩ := List.append_inj addrMap (by simp [rootsLen, lens])
  have positive : sp0 + sp1 ≠ 0 := by omega
  have found := absInv1.2.2.2.1.1 positive
  obtain ⟨pre, post, heapShape, aEq⟩ := heapLookup_split heap a _ found
  have expand : (heapExpand (sp0 + sp1) : ValueHeap width) = [.unused (sp0 + sp1 - 1)] := by
    unfold heapExpand
    rw [if_neg positive]
  have heapOld : heap = pre ++ heapExpand (sp0 + sp1) ++ post := by
    simpa [expand, List.append_assoc] using heapShape
  have elen : elLength (blockRep (β := WordLocW width) tag rs) = ws.length + 1 := by
    simp [blockRep, elLength, rootsLen, lens]
  have heap2Shape : heap2 = pre ++ [blockRep tag rs] ++ heapExpand (sp0 + sp1 - (ws.length + 1)) ++ post := by
    have store := stored
    classical
    unfold heapStoreUnusedAlt at store
    simp only [found, show elLength (blockRep (β := WordLocW width) tag rs) ≤ sp0 + sp1 by omega,
      and_self, ↓reduceIte] at store
    rw [heapShape, aEq, heapStore_atPrefix] at store
    have h := congrArg Prod.fst store
    simpa [elen, List.append_assoc] using h.symm
  obtain ⟨heapBound, byteBound, shiftBound, lenPos, lenBound, shiftWidth, globals, curr, other,
    currAligned, otherAligned, currLookup, otherLookup, freeLookup, triggerLookup, endLookup,
    heapLenLookup, globInv, genInv, heapSep⟩ := heapMem
  have heapSepOld : SetSep.star (wordHeap curr (pre ++ heapExpand (sp0 + sp1) ++ post) c)
      (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m, fun x => dm x = true)) := by
    simpa [heapOld] using heapSep
  obtain ⟨m1, run, heapSepNew⟩ := wordHeapAlloc c curr pre post (sp0 + sp1) (blockRep tag rs) ws hd
    (wordHeap other (heapExpand limit) c) m dm (by omega) elen
    (wordElBlockEq c _ tag rs ws hd mapped encoded (by omega) good) heapSepOld
  have nLen : heapLength heap2 = heapLength heap :=
    heapStoreUnusedAlt_imp_length a (sp0 + sp1) (blockRep tag rs) heap heap2 stored
  let free := curr + StackRemove.bytesInWord width * BitVec.ofNat width a
  let newFree := free + wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)
  let st1 := st.update (.nextFree, .word newFree)
  have nstore : st1.lookup .nextFree = some (.word newFree) := by
    simp [st1, HolFiniteMapExact.update, FUPDATE]
  have shapeSep : SetSep.star (wordHeap curr heap2 c) (wordHeap other (heapExpand limit) c)
      (SetSep.fun2Set (m1, fun x => dm x = true)) := by simpa [heap2Shape] using heapSepNew
  have spFit : ws.length + 1 ≤ sp0 := by omega
  have addSub : a + (ws.length + 1) + (sp0 - (ws.length + 1)) = a + sp0 := by omega
  have addSub1 : a + (ws.length + 1) + (sp0 - (ws.length + 1)) + sp1 = a + sp0 + sp1 := by omega
  have nfreeEq : newFree = curr + StackRemove.bytesInWord width * BitVec.ofNat width (a + (ws.length + 1)) := by
    simp only [newFree, free, wordSemBytesInWord, StackRemove.bytesInWord, BitVec.ofNat_add, BitVec.mul_add]
    rw [BitVec.add_assoc]
  have heapMem1 : heapInMemoryStore heap2 (a + (ws.length + 1)) (sp0 - (ws.length + 1)) sp1 gens c st1 m1 dm limit := by
    refine ⟨by simpa [nLen] using heapBound, by simpa [nLen] using byteBound, shiftBound, lenPos, lenBound, shiftWidth, ?_, curr, other,
      currAligned, otherAligned, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, shapeSep⟩
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using globals
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using currLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using otherLookup
    · simpa [nfreeEq] using nstore
    · simpa [st1, HolFiniteMapExact.update, FUPDATE, addSub] using triggerLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE, addSub1] using endLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using heapLenLookup
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using globInv
    · simpa [st1, HolFiniteMapExact.update, FUPDATE] using genInv
  have ptrEq : wordAddr c (.pointer a (.word (ptrBits c tag vals.length))) =
      Build.makeConsPtr c (free - curr) tag ws.length := by
    have stride : StackRemove.bytesInWord width * BitVec.ofNat width a =
        (BitVec.ofNat width a <<< wordShiftAmount width) := by
      rcases good with h | h <;> subst width <;> apply BitVec.eq_of_toNat_eq <;>
        simp [StackRemove.bytesInWord, wordShiftAmount, BitVec.toNat_mul,
          BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_mod]
    have delta : free - curr = StackRemove.bytesInWord width * BitVec.ofNat width a := by
      simp [free]
    have shifts : wordShiftAmount width + (shiftLength c - wordShiftAmount width) = shiftLength c := by omega
    rw [makeConsPtr_eq, delta, stride, ← BitVec.shiftLeft_add, shifts, ← lens]
    simp only [wordAddr, getAddr, getLowerBits_ptrBits, WordLocW.word.injEq]
    ac_rfl
  have afterRoots : List.Forall₂ (fun address word => wordAddr c address = word) roots2 (vars.map Prod.snd) :=
    (every2_function_eq roots2 (vars.map Prod.snd) (wordAddr c)).mpr tailMap
  have wordInv1 : wordMlInv (heap2, be, a + (ws.length + 1), sp0 - (ws.length + 1), sp1, gens) limit ts c
      (sptInsert ptr (.mutBlock tag false (vals.take index) (holEl index vals) (vals.drop (index + 1))) refs)
      ((.refPtr false ptr, Build.makeConsPtr c (free - curr) tag ws.length) :: vars) := by
    refine ⟨.pointer a (.word (ptrBits c tag vals.length)) :: roots2, ?_, ?_⟩
    · simpa [blockRep, elLength, rootsLen, lens] using absAfter
    · simp only [List.map_cons]
      exact List.Forall₂.cons ptrEq afterRoots
  refine ⟨free, curr, m1, ?_, currLookup, ?_, ?_⟩
  · simpa [free] using freeLookup
  · simpa [free, aEq] using run
  · change memoryRel c be ts (sptInsert ptr (.mutBlock tag false (vals.take index) (holEl index vals) (vals.drop (index + 1))) refs) (sp - (ws.length + 1)) st1 m1 dm _
    exact ⟨heap2, limit, a + (ws.length + 1), sp0 - (ws.length + 1), sp1, gens,
      heapMem1, wordInv1, limitBound, by omega⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

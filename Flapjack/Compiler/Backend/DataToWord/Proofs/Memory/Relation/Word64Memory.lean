module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConsMemory
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Proof
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64Concrete
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Allocate a Word64 cell while preserving the complete data-to-word memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Word64_alt"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_word64Alt {width : Nat} [NeZero width] (c : DataToWord.Config) (be : Bool)
    (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (vs vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (word : BitVec 64) (ws : List (WordLocW width)) (hd : BitVec width)
    (rel : memoryRel c be ts refs sp st m dm (vs ++ vars)) (good : goodDimindex width)
    (rep : (word64Rep word : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) =
      .dataElement [] ws.length (.word64Tag, ws))
    (enough : ws.length < sp) (encoded : DataToWord.encodeHeader c 3 ws.length = some hd) :
    ∃ ne curr m1, st.lookup .nextFree = some (.word ne) ∧ st.lookup .currHeap = some (.word curr) ∧
      storeList ne (.word hd :: ws) m dm = some m1 ∧
      memoryRel c be ts refs (sp - (ws.length + 1))
        (st.update (.nextFree, .word (ne + wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)))) m1 dm
        ((.word64 word, Build.makePtr c (ne - curr) (0 : BitVec width) ws.length) :: vars) := by
  obtain ⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩ := rel
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  have absInv1 : absMlInv c (vs.map Prod.fst ++ vars.map Prod.fst) refs
      (roots, heap, be, a, sp0, sp1, gens) limit ts := by
    simpa [List.map_append] using absInv
  obtain ⟨rs, roots2, rootsEq, rootsLen⟩ :=
    split1Thm c (vs.map Prod.fst) (vars.map Prod.fst) refs roots heap be a sp0 sp1 gens limit ts absInv1
  have absSplit : absMlInv c (vs.map Prod.fst ++ vars.map Prod.fst) refs
      (rs ++ roots2, heap, be, a, sp0, sp1, gens) limit ts := by simpa [rootsEq] using absInv1
  obtain ⟨heap2, stored, absAfter⟩ := word64Alt c (vs.map Prod.fst) (vars.map Prod.fst) refs rs roots2
    heap be a sp0 sp1 gens limit ts word ws.length ws absSplit (by simpa using rootsLen.symm) rep (by omega)
  have addrMap : roots.map (wordAddr c) = vs.map Prod.snd ++ vars.map Prod.snd := by
    have h := (every2_function_eq roots ((vs ++ vars).map Prod.snd) (wordAddr c)).mp addresses
    simpa [List.map_append] using h
  rw [rootsEq, List.map_append] at addrMap
  have ⟨mapped, tailMap⟩ := List.append_inj addrMap (by simpa using rootsLen)
  have positive : sp0 + sp1 ≠ 0 := by omega
  have found := absInv1.2.2.2.1.1 positive
  obtain ⟨pre, post, heapShape, aEq⟩ := heapLookup_split heap a _ found
  have expand : (heapExpand (sp0 + sp1) : ValueHeap width) = [.unused (sp0 + sp1 - 1)] := by
    unfold heapExpand
    rw [if_neg positive]
  have heapOld : heap = pre ++ heapExpand (sp0 + sp1) ++ post := by
    simpa [expand, List.append_assoc] using heapShape
  have storedCell : heapStoreUnusedAlt a (sp0 + sp1) (.dataElement [] ws.length (.word64Tag, ws)) heap = (heap2, true) := by
    simpa [rep] using stored
  have heap2Shape : heap2 = pre ++ [.dataElement [] ws.length (.word64Tag, ws)] ++ heapExpand (sp0 + sp1 - (ws.length + 1)) ++ post := by
    have store := storedCell
    classical
    simp only [heapStoreUnusedAlt, found, show elLength (.dataElement [] ws.length (.word64Tag, ws) : HeapElement (WordLocW width) (HeapTag × List (WordLocW width))) ≤ sp0 + sp1 by simp [elLength]; omega,
      and_self, ↓reduceIte] at store
    rw [heapShape, aEq, heapStore_atPrefix] at store
    have h := congrArg Prod.fst store
    simpa [elLength, List.append_assoc] using h.symm
  obtain ⟨heapBound, byteBound, shiftBound, lenPos, lenBound, shiftWidth, globals, curr, other,
    currAligned, otherAligned, currLookup, otherLookup, freeLookup, triggerLookup, endLookup,
    heapLenLookup, globInv, genInv, heapSep⟩ := heapMem
  have heapSepOld : SetSep.star (wordHeap curr (pre ++ heapExpand (sp0 + sp1) ++ post) c)
      (wordHeap other (heapExpand limit) c) (SetSep.fun2Set (m, fun x => dm x = true)) := by
    simpa [heapOld] using heapSep
  obtain ⟨m1, run, heapSepNew⟩ := wordHeapAlloc c curr pre post (sp0 + sp1)
    (.dataElement [] ws.length (.word64Tag, ws)) ws hd (wordHeap other (heapExpand limit) c) m dm
    (by omega) (by simp [elLength]) (wordElWord64Eq c _ ws hd encoded (by omega) good) heapSepOld
  have nLen : heapLength heap2 = heapLength heap :=
    heapStoreUnusedAlt_imp_length a (sp0 + sp1) (word64Rep word) heap heap2 stored
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
  have ptrEq : wordAddr c (.pointer a (.word 0)) =
      Build.makePtr c (free - curr) (0 : BitVec width) ws.length := by
    have stride : StackRemove.bytesInWord width * BitVec.ofNat width a =
        (BitVec.ofNat width a <<< wordShiftAmount width) := by
      rcases good with h | h <;> subst width <;> apply BitVec.eq_of_toNat_eq <;>
        simp [StackRemove.bytesInWord, wordShiftAmount, BitVec.toNat_mul,
          BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_mod]
    have delta : free - curr = StackRemove.bytesInWord width * BitVec.ofNat width a := by simp [free]
    have shifts : wordShiftAmount width + (shiftLength c - wordShiftAmount width) = shiftLength c := by omega
    simp only [Build.makePtr, delta, stride, ← BitVec.shiftLeft_add, shifts, wordAddr, getAddr, getLowerBits]
    simp
  have afterRoots : List.Forall₂ (fun address word => wordAddr c address = word) roots2 (vars.map Prod.snd) :=
    (every2_function_eq roots2 (vars.map Prod.snd) (wordAddr c)).mpr tailMap
  have wordInv1 : wordMlInv (heap2, be, a + (ws.length + 1), sp0 - (ws.length + 1), sp1, gens) limit ts c refs
      ((.word64 word, Build.makePtr c (free - curr) (0 : BitVec width) ws.length) :: vars) := by
    refine ⟨.pointer a (.word 0) :: roots2, ?_, ?_⟩
    · simpa [Nat.add_assoc, Nat.sub_sub] using absAfter
    · simp only [List.map_cons]
      exact List.Forall₂.cons ptrEq afterRoots
  refine ⟨free, curr, m1, ?_, currLookup, ?_, ?_⟩
  · simpa [free] using freeLookup
  · simpa [free, aEq] using run
  · change memoryRel c be ts refs (sp - (ws.length + 1)) st1 m1 dm _
    exact ⟨heap2, limit, a + (ws.length + 1), sp0 - (ws.length + 1), sp1, gens,
      heapMem1, wordInv1, limitBound, by omega⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

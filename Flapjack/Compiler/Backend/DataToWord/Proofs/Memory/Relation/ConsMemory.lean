module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConcreteAlloc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.PointerBits
public import Flapjack.Compiler.Backend.DataToWord.Build
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConsAlt
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StoreListThm
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.HeaderDecode
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Allocating a nonempty constructor preserves the complete data-to-word memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Cons1"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_cons1 {width : Nat} [NeZero width] (c : DataToWord.Config) (be : Bool)
    (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (vals : List Flapjack.Compiler.Backend.DataSem.Value) (ws : List (WordLocW width))
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (tag : Nat) (hd : BitVec width)
    (rel : memoryRel c be ts refs sp st m dm (vals.zip ws ++ vars))
    (lens : vals.length = ws.length) (nonempty : vals ≠ [])
    (encoded : DataToWord.encodeHeader c (4 * tag) ws.length = some hd)
    (enough : ws.length < sp) (good : goodDimindex width) :
    ∃ free curr m1, st.lookup .nextFree = some (.word free) ∧ st.lookup .currHeap = some (.word curr) ∧
      storeList free (.word hd :: ws) m dm = some m1 ∧
      memoryRel c be (ts + 1) refs (sp - (ws.length + 1))
        (st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width (ws.length + 1)))) m1 dm
        ((.block ts tag vals, Build.makeConsPtr c (free - curr) tag ws.length) :: vars) := by
  obtain ⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩ := rel
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  have absInv1 : absMlInv c (vals ++ vars.map Prod.fst) refs
      (roots, heap, be, a, sp0, sp1, gens) limit ts := by
    simpa [List.map_append, List.map_fst_zip (Nat.le_of_eq lens)] using absInv
  obtain ⟨rs, roots2, heap2, rootsEq, rootsLen, stored, absAfter⟩ :=
    consThm_alt (β := WordLocW width) (γ := WordLocW width) c vals (vars.map Prod.fst) refs roots heap be a sp0 sp1 gens limit ts tag
      absInv1 (by omega) nonempty
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
  obtain ⟨m1, run, heapSepNew⟩ := wordHeapAlloc c curr pre post (sp0 + sp1) tag rs ws hd
    (wordHeap other (heapExpand limit) c) m dm (by omega) mapped encoded (by omega) good heapSepOld
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
  have wordInv1 : wordMlInv (heap2, be, a + (ws.length + 1), sp0 - (ws.length + 1), sp1, gens) limit (ts + 1) c refs
      ((.block ts tag vals, Build.makeConsPtr c (free - curr) tag ws.length) :: vars) := by
    refine ⟨.pointer a (.word (ptrBits c tag vals.length)) :: roots2, ?_, ?_⟩
    · simpa [blockRep, elLength, rootsLen, lens] using absAfter
    · simp only [List.map_cons]
      exact List.Forall₂.cons ptrEq afterRoots
  refine ⟨free, curr, m1, ?_, currLookup, ?_, ?_⟩
  · simpa [free] using freeLookup
  · simpa [free, aEq] using run
  · change memoryRel c be (ts + 1) refs (sp - (ws.length + 1)) st1 m1 dm _
    exact ⟨heap2, limit, a + (ws.length + 1), sp0 - (ws.length + 1), sp1, gens,
      heapMem1, wordInv1, limitBound, by omega⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

module
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ConcreteLeafAlloc
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshByteProof
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteConcrete
@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.DataSem Flapjack.Compiler.Backend.GcCombined

/-- Fresh byte-array allocation preserves the complete data-to-word memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_RefByte_content"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_freshByte {width : Nat} [NeZero width] (c : DataToWord.Config) (be : Bool)
    (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (sp : Nat) (st : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (m : BitVec width → WordLocW width) (dm : BitVec width → Bool)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (ptr n : Nat) (flag : Bool) (bytes : List (BitVec 8))
    (rel : memoryRel c be ts refs sp st m dm vars) (fresh : ¬ sptDomain refs ptr)
    (enough : Build.byteLen width n < sp) (countBound : Build.byteLen width n < 2 ^ (width - 4))
    (lenBound : Build.byteLen width n < 2 ^ c.lenSize) (bytesLen : n = bytes.length)
    (good : goodDimindex width) :
    ∃ free curr m1, st.lookup .nextFree = some (.word free) ∧ st.lookup .currHeap = some (.word curr) ∧
      storeList free (.word (makeByteHeader c flag n) ::
        (writeBytes bytes (List.replicate (Build.byteLen width n) (0 : BitVec width)) be).map .word) m dm = some m1 ∧
      memoryRel c be ts (sptInsert ptr (.byteArray flag bytes) refs) (sp - (Build.byteLen width n + 1))
        (st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width (Build.byteLen width n + 1)))) m1 dm
        ((.refPtr true ptr, Build.makePtr c (free - curr) (0 : BitVec width) (Build.byteLen width n)) :: vars) := by
  let count := Build.byteLen width n
  have countEq : count = bytes.length / (width / 8) + 1 := by
    subst n
    rcases good with hw | hw <;> subst width <;> simp [count, Build.byteLen]
  let packed := writeBytes bytes (List.replicate count (0 : BitVec width)) be
  have packedLen : packed.length = count := by simp [packed, writeBytes_wordCount]
  obtain ⟨heap, limit, a, sp0, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩ := rel
  obtain ⟨roots, absInv, addresses⟩ := wordInv
  obtain ⟨heap2, stored, absAfter⟩ := newByteAlt c (vars.map Prod.fst) refs roots heap be a sp0 sp1 gens limit ts
    count ptr flag true bytes absInv countEq fresh (by dsimp [count] at *; omega)
  have cellEq : bytesRep be flag bytes (List.replicate count 0) =
      .dataElement [] count (.bytesTag flag bytes.length, packed.map .word) := by
    simp [bytesRep, packed, writeBytes_wordCount]
  have storedCell : heapStoreUnusedAlt a (sp0 + sp1)
      (.dataElement [] (packed.map WordLocW.word).length (.bytesTag flag bytes.length, packed.map .word)) heap = (heap2, true) := by
    rw [List.length_map, packedLen, ← cellEq]
    exact stored
  have heapMemCopy := heapMem
  obtain ⟨heapBound, byteBound, shiftBound, lenPos, configBound, shiftWidth, globals, oldCurr, other,
    currAligned, otherAligned, oldCurrLookup, otherLookup, oldFreeLookup, triggerLookup, endLookup,
    heapLenLookup, globInv, genInv, heapSep⟩ := heapMemCopy
  have cell : ∀ (addr : BitVec width), wordEl addr (.dataElement [] (packed.map WordLocW.word).length
      (.bytesTag flag bytes.length, packed.map .word)) c =
      Misc.wordList addr (.word (makeByteHeader c flag bytes.length) :: packed.map .word) := by
    intro addr
    have h := wordElBytesEq c addr bytes be flag good configBound
      (by simpa [← countEq, count, bytesLen] using countBound)
      (by simpa [← countEq, count, bytesLen] using lenBound)
    simpa [bytesRep, packed, packedLen, writeBytes_wordCount, countEq] using h
  obtain ⟨free, curr, m1, freeLookup, currLookup, freeEq, run, heapMem1⟩ :=
    heapInMemoryStore_allocateLeaf c heap heap2 a sp0 sp1 gens st m dm limit (.bytesTag flag bytes.length)
      (packed.map .word) (makeByteHeader c flag bytes.length) absInv.2.2.2.1
      (by simp only [List.length_map, packedLen]; dsimp [count] at *; omega) storedCell cell heapMem
  let st1 := st.update (.nextFree, .word (free + wordSemBytesInWord * BitVec.ofNat width (count + 1)))
  have ptrEq : wordAddr c (.pointer a (.word 0)) = Build.makePtr c (free - curr) (0 : BitVec width) count := by
    have stride : StackRemove.bytesInWord width * BitVec.ofNat width a =
        (BitVec.ofNat width a <<< wordShiftAmount width) := by
      rcases good with h | h <;> subst width <;> apply BitVec.eq_of_toNat_eq <;>
        simp [StackRemove.bytesInWord, wordShiftAmount, BitVec.toNat_mul,
          BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.mul_comm, Nat.mul_mod]
    have delta : free - curr = StackRemove.bytesInWord width * BitVec.ofNat width a := by simp [freeEq]
    have shifts : wordShiftAmount width + (shiftLength c - wordShiftAmount width) = shiftLength c := by omega
    simp only [Build.makePtr, delta, stride, ← BitVec.shiftLeft_add, shifts, wordAddr, getAddr, getLowerBits]
    simp
  have wordInv1 : wordMlInv (heap2, be, a + (count + 1), sp0 - (count + 1), sp1, gens) limit ts c
      (sptInsert ptr (.byteArray flag bytes) refs)
      ((.refPtr true ptr, Build.makePtr c (free - curr) (0 : BitVec width) count) :: vars) := by
    refine ⟨.pointer a (.word 0) :: roots, ?_, ?_⟩
    · simpa [Nat.add_assoc] using absAfter
    · simp only [List.map_cons]
      exact List.Forall₂.cons ptrEq addresses
  refine ⟨free, curr, m1, freeLookup, currLookup, ?_, ?_⟩
  · simpa [packed, count, bytesLen] using run
  · change memoryRel c be ts (sptInsert ptr (.byteArray flag bytes) refs) (sp - (count + 1)) st1 m1 dm _
    exact ⟨heap2, limit, a + (count + 1), sp0 - (count + 1), sp1, gens,
      by simpa [st1, packedLen] using heapMem1, wordInv1, limitBound, by dsimp [count] at *; omega⟩
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

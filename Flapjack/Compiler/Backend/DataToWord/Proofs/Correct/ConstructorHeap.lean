import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorFree
import Flapjack.Compiler.Backend.GcShared.Filter
import Flapjack.Compiler.Backend.DataToWord.Proofs.Numbers

/-! Reconstruction of the separated word heap after constructor writes. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- Successful compiler header encoding provides the block payload and its
word-heap length bound. -/
theorem encodedConstructor_payload {width : Nat} [NeZero width] (conf : Config)
    (addresses : List (HeapAddress (WordLocW width))) (tag : Nat) (header : BitVec width)
    (encoded : encodeHeader conf (4 * tag) addresses.length = some header) :
    wordPayload addresses addresses.length (.blockTag tag) [] conf =
        (header, addresses.map (wordAddr conf), true) ∧ addresses.length < 2 ^ (width - 4) := by
  have tagEq : (BitVec.ofNat width tag <<< (2 : Nat)) = BitVec.ofNat width (4 * tag) := by
    simpa [Nat.mul_comm] using (shift_eq_inlined (width := width) tag 2)
  have headerEq : makeHeader conf (BitVec.ofNat width (4 * tag)) addresses.length = header := by
    unfold encodeHeader at encoded
    split at encoded <;> simp_all
  have bound : addresses.length < 2 ^ (width - 4) := by
    unfold encodeHeader at encoded
    split at encoded <;> simp_all
  refine ⟨?_, bound⟩
  simp only [wordPayload, tagEq, Nat.mul_comm tag 4, headerEq, List.isEmpty_nil,
    true_and, encoded, decide_true, Bool.and_self]

/-- Writing a valid constructor header and fields into the front of an
unused region produces the corresponding separated word heap. This is
Flapjack simulation infrastructure. -/
theorem wordHeap_storeConstructor {width : Nat} [NeZero width] (conf : Config)
    (pre post : ValueHeap width) (addresses : List (HeapAddress (WordLocW width)))
    (tag free : Nat) (header : BitVec width) (curr : BitVec width)
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (enough : addresses.length + 1 ≤ free)
    (payload : wordPayload addresses addresses.length (.blockTag tag) [] conf =
      (header, addresses.map (wordAddr conf), true))
    (lengthBound : addresses.length < 2 ^ (width - 4))
    (decoded : WordGcFunctions.decodeLength conf header = BitVec.ofNat width addresses.length)
    (separated : SetSep.star (wordHeap curr (pre ++ heapExpand free ++ post) conf) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
    SetSep.star (wordHeap curr
      (pre ++ [blockRep tag addresses] ++ heapExpand (free - (addresses.length + 1)) ++ post) conf) frame
      (SetSep.fun2Set (storeEachMemory base 0 (.word header :: addresses.map (wordAddr conf)) memory,
        fun addr => domain addr = true)) := by
  let count := addresses.length + 1
  let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
  have sum : free = count + (free - count) := by dsimp [count]; omega
  rw [List.append_assoc, wordHeapAppend, wordHeapAppend, wordHeap_heapExpand] at separated
  rw [sum, StackRemove.Proofs.WordListMemory.wordListExistsAdd] at separated
  rw [← SetSep.starAssoc, ← SetSep.starAssoc, star_swap_first, ← SetSep.starAssoc] at separated
  have freeWords : SetSep.star (Misc.wordListExists (base + 0) (.word header :: addresses.map (wordAddr conf)).length)
      (SetSep.star (Misc.wordListExists (base + StackRemove.bytesInWord width * BitVec.ofNat width count) (free - count))
        (SetSep.star (wordHeap curr pre conf)
          (SetSep.star (wordHeap (base + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength (heapExpand free : ValueHeap width))) post conf) frame)))
      (SetSep.fun2Set (memory, fun addr => domain addr = true)) := by
    simpa [base, count, ← sum] using separated
  have written := storeEachMemory_wordList base 0 (.word header :: addresses.map (wordAddr conf)) memory domain _ freeWords
  rw [star_swap_first (Misc.wordListExists _ _) (wordHeap curr pre conf),
    star_swap_first (Misc.wordList _ _) (wordHeap curr pre conf)] at written
  have element : wordEl base (blockRep tag addresses) conf =
      Misc.wordList base (.word header :: addresses.map (wordAddr conf)) := by
    funext h
    apply propext
    simp only [wordEl, blockRep, payload, List.length_map]
    rw [StackRemove.WordListExists.starCond]
    simp [lengthBound, decoded]
  simp only [List.append_assoc, List.singleton_append]
  rw [wordHeapAppend]
  simp only [List.cons_append]
  have step : wordHeap base (blockRep tag addresses :: (heapExpand (free - count) ++ post)) conf =
      SetSep.star (wordEl base (blockRep tag addresses) conf)
        (wordHeap (base + StackRemove.bytesInWord width * BitVec.ofNat width (elLength (blockRep tag addresses)))
          (heapExpand (free - count) ++ post) conf) := rfl
  rw [step]
  rw [element, wordHeapAppend, wordHeap_heapExpand]
  simp only [← SetSep.starAssoc]
  have remaining : addresses.length + 1 + (free - (addresses.length + 1)) = free := by omega
  simpa [base, count, heapLength_heapExpand, elLength, blockRep, List.append_assoc,
    BitVec.add_assoc, ← BitVec.mul_add, ← BitVec.ofNat_add, Nat.add_assoc, remaining] using written

/-- After the constructor stores and `nextFree` update, the complete
heap/store relation reflects the allocated cell and remaining free space.
The header conditions are the concrete encoding obligations of the compiler. -/
theorem heapInMemoryStore_storeConstructor {width : Nat} [NeZero width] (conf : Config)
    (pre post : ValueHeap width) (addresses : List (HeapAddress (WordLocW width)))
    (tag sp sp1 : Nat) (header : BitVec width) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (limit : Nat) (enough : addresses.length + 1 ≤ sp)
    (payload : wordPayload addresses addresses.length (.blockTag tag) [] conf =
      (header, addresses.map (wordAddr conf), true))
    (lengthBound : addresses.length < 2 ^ (width - 4))
    (decoded : WordGcFunctions.decodeLength conf header = BitVec.ofNat width addresses.length)
    (heapMem : heapInMemoryStore (pre ++ heapExpand (sp + sp1) ++ post)
      (heapLength pre) sp sp1 gens conf store memory domain limit) :
    ∃ curr, store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre))) ∧
      let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
      let next := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre + (addresses.length + 1))
      heapInMemoryStore (pre ++ [blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1)) ++ post)
        (heapLength pre + (addresses.length + 1)) (sp - (addresses.length + 1)) sp1 gens conf
        (store.updateEq (.nextFree, .word next))
        (storeEachMemory base 0 (.word header :: addresses.map (wordAddr conf)) memory) domain limit := by
  obtain ⟨bound1, bound2, shift, lenNonzero, lenBound, shiftBound, globals,
    curr, other, currAligned, otherAligned, currStore, otherStore, nextStore,
    triggerStore, endStore, lengthStore, globInv, genInv, separated⟩ := heapMem
  have wordHeapNew := wordHeap_storeConstructor conf pre post addresses tag (sp + sp1) header curr memory domain _
    (by omega) payload lengthBound decoded separated
  have lengthEq : heapLength (pre ++ heapExpand (sp + sp1) ++ post) =
      heapLength (pre ++ [blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1)) ++ post) := by
    simp only [heapLength_append, heapLength_heapExpand]
    have one : heapLength [blockRep (β := WordLocW width) tag addresses] = addresses.length + 1 := by
      simp [heapLength, blockRep, elLength]
    rw [one]
    omega
  have triggerEq : heapLength pre + sp =
      (heapLength pre + (addresses.length + 1)) + (sp - (addresses.length + 1)) := by omega
  have endEq : heapLength pre + sp + sp1 =
      (heapLength pre + (addresses.length + 1)) + (sp - (addresses.length + 1)) + sp1 := by omega
  refine ⟨curr, nextStore, ?_⟩
  dsimp only
  refine ⟨?_, ?_, shift, lenNonzero, lenBound, shiftBound, ?_, curr, other, currAligned, otherAligned,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, wordHeapNew⟩
  · simpa only [← lengthEq] using bound1
  · simpa only [← lengthEq] using bound2
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using globals
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using currStore
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using otherStore
  · simp [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ← triggerEq] using triggerStore
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, ← endEq] using endStore
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using lengthStore
  · simpa [globRealInv, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using globInv
  · simpa [HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using genInv

/-- The compiler's successful header encoding discharges the payload and
length obligations of the heap/store update. -/
theorem heapInMemoryStore_storeConstructor_of_encoded {width : Nat} [NeZero width] (conf : Config)
    (pre post : ValueHeap width) (addresses : List (HeapAddress (WordLocW width)))
    (tag sp sp1 : Nat) (header : BitVec width) (gens : GcCombined.GenState)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (limit : Nat) (enough : addresses.length + 1 ≤ sp)
    (encoded : encodeHeader conf (4 * tag) addresses.length = some header)
    (decoded : WordGcFunctions.decodeLength conf header = BitVec.ofNat width addresses.length)
    (heapMem : heapInMemoryStore (pre ++ heapExpand (sp + sp1) ++ post)
      (heapLength pre) sp sp1 gens conf store memory domain limit) :
    ∃ curr, store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre))) ∧
      let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
      let next := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre + (addresses.length + 1))
      heapInMemoryStore (pre ++ [blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1)) ++ post)
        (heapLength pre + (addresses.length + 1)) (sp - (addresses.length + 1)) sp1 gens conf
        (store.updateEq (.nextFree, .word next))
        (storeEachMemory base 0 (.word header :: addresses.map (wordAddr conf)) memory) domain limit := by
  obtain ⟨payload, lengthBound⟩ := encodedConstructor_payload conf addresses tag header encoded
  exact heapInMemoryStore_storeConstructor conf pre post addresses tag sp sp1 header gens store memory domain limit
    enough payload lengthBound decoded heapMem

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct

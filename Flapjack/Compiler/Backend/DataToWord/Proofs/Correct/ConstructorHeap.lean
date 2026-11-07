import Flapjack.Compiler.Backend.DataToWord.Proofs.Correct.ConstructorFree
import Flapjack.Compiler.Backend.GcShared.Filter
import Flapjack.Compiler.Backend.DataToWord.Proofs.Numbers
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockHeaderInjective
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.FreshBlockGc

/-! Reconstruction of the separated word heap after constructor writes. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Correct
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A successfully encoded header decodes to its original length under the
configuration bounds used by the word heap. -/
theorem decodeLength_encodeHeader {width : Nat} [NeZero width] (conf : Config)
    (tag len : Nat) (header : BitVec width) (widthBound : 4 ≤ width)
    (configBound : conf.lenSize + 2 < width)
    (encoded : encodeHeader conf tag len = some header) :
    WordGcFunctions.decodeLength conf header = BitVec.ofNat width len := by
  have bounds : tag < 2 ^ (width - conf.lenSize - 2) ∧ tag < 2 ^ width / 16 ∧
      len < 2 ^ (width - 4) ∧ len < 2 ^ conf.lenSize := by
    by_contra no
    simp [encodeHeader, no] at encoded
  have headerEq : makeHeader conf (BitVec.ofNat width tag) len = header := by
    simpa [encodeHeader, bounds] using encoded
  rw [← headerEq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [WordGcFunctions.decodeLength, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ofNat,
    hi, decide_true, Bool.true_and]
  by_cases low : i < conf.lenSize
  · have position : width - conf.lenSize + i = i + (width - conf.lenSize) := by omega
    rw [position, headerLengthBit conf tag len i widthBound configBound bounds.1 low]
  · have out : ¬width - conf.lenSize + i < width := by omega
    have pow : 2 ^ conf.lenSize ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
    have zero : len.testBit i = false := Nat.testBit_lt_two_pow (by omega)
    rw [BitVec.getLsbD_of_ge _ _ (by omega), zero]

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
    ∃ curr, store.lookup .currHeap = some (.word curr) ∧
      store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre))) ∧
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
  refine ⟨curr, currStore, nextStore, ?_⟩
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
    (heapMem : heapInMemoryStore (pre ++ heapExpand (sp + sp1) ++ post)
      (heapLength pre) sp sp1 gens conf store memory domain limit) :
    ∃ curr, store.lookup .currHeap = some (.word curr) ∧
      store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre))) ∧
      let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
      let next := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre + (addresses.length + 1))
      heapInMemoryStore (pre ++ [blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1)) ++ post)
        (heapLength pre + (addresses.length + 1)) (sp - (addresses.length + 1)) sp1 gens conf
        (store.updateEq (.nextFree, .word next))
        (storeEachMemory base 0 (.word header :: addresses.map (wordAddr conf)) memory) domain limit := by
  obtain ⟨payload, lengthBound⟩ := encodedConstructor_payload conf addresses tag header encoded
  have configBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have decoded := decodeLength_encodeHeader conf (4 * tag) addresses.length header (by omega) (by omega) encoded
  exact heapInMemoryStore_storeConstructor conf pre post addresses tag sp sp1 header gens store memory domain limit
    enough payload lengthBound decoded heapMem

/-- Constructor allocation preserves the word-level ML invariant, with the
new source block and its projected target pointer added to the stack. -/
theorem wordMlInv_allocateBlock {width : Nat} [NeZero width] (conf : Config)
    (fields vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (pre post : ValueHeap width) (sp sp1 next tag limit : Nat) (be : Bool) (gens : GcCombined.GenState)
    (nonempty : fields ≠ []) (enough : fields.length + 1 ≤ sp)
    (inv : wordMlInv (pre ++ heapExpand (sp + sp1) ++ post, be, heapLength pre, sp, sp1, gens)
      limit next conf refs (fields ++ vars)) :
    ∃ addresses,
      addresses.length = fields.length ∧
      List.Forall₂ (fun address word => wordAddr conf address = word) addresses (fields.map Prod.snd) ∧
      wordMlInv (pre ++ [blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1)) ++ post,
        be, heapLength pre + (addresses.length + 1), sp - (addresses.length + 1), sp1, gens)
        limit (next + 1) conf refs
        (((.block next tag (fields.map Prod.fst)),
          wordAddr conf (.pointer (heapLength pre) (.word (ptrBits conf tag addresses.length)))) :: fields ++ vars) := by
  obtain ⟨roots, absInv, projected⟩ := inv
  have rootLength : roots.length = (fields ++ vars).length := by
    simpa using projected.length_eq
  let addresses := roots.take fields.length
  let rest := roots.drop fields.length
  have addressesLength : addresses.length = fields.length := by
    simp [addresses, rootLength]
  have parts : roots = addresses ++ rest := by simp [addresses, rest]
  have fieldsProjected : List.Forall₂ (fun address word => wordAddr conf address = word) addresses (fields.map Prod.snd) := by
    have selected := List.forall₂_take fields.length projected
    simpa [addresses] using selected
  have sourceNonempty : fields.map Prod.fst ≠ [] := by simpa using nonempty
  have oldAbs : absMlInv conf (fields.map Prod.fst ++ vars.map Prod.fst) refs
      (addresses ++ rest, pre ++ heapExpand (sp + sp1) ++ post, be, heapLength pre, sp, sp1, gens) limit next := by
    simpa [List.map_append, ← parts] using absInv
  have nextAbs := absMlInv_allocateBlock conf (fields.map Prod.fst) (vars.map Prod.fst) addresses rest refs pre post
    sp sp1 next tag limit be gens sourceNonempty (by simp [addressesLength]) (by omega) oldAbs
  refine ⟨addresses, addressesLength, fieldsProjected, ?_⟩
  refine ⟨.pointer (heapLength pre) (.word (ptrBits conf tag addresses.length)) :: roots, ?_, ?_⟩
  · simpa [List.map_append, ← parts] using nextAbs
  · exact .cons rfl projected

/-- The abstract and concrete constructor updates together establish the
full memory relation with reduced available space. -/
theorem memoryRel_allocateBlock_from_heap {width : Nat} [NeZero width] (conf : Config)
    (fields vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (pre post : ValueHeap width) (sp sp1 next tag limit space : Nat) (be : Bool) (gens : GcCombined.GenState)
    (header : BitVec width) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (nonempty : fields ≠ []) (enough : fields.length + 1 ≤ sp) (spaceBound : space ≤ sp)
    (limitBound : (limit + 3) * (width / 8) + 1 < 2 ^ width)
    (encoded : encodeHeader conf (4 * tag) fields.length = some header)
    (heapMem : heapInMemoryStore (pre ++ heapExpand (sp + sp1) ++ post)
      (heapLength pre) sp sp1 gens conf store memory domain limit)
    (inv : wordMlInv (pre ++ heapExpand (sp + sp1) ++ post, be, heapLength pre, sp, sp1, gens)
      limit next conf refs (fields ++ vars)) :
    ∃ (curr : BitVec width) (addresses : List (HeapAddress (WordLocW width))),
      store.lookup .currHeap = some (.word curr) ∧
      store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre))) ∧
      addresses.length = fields.length ∧
      addresses.map (wordAddr conf) = fields.map Prod.snd ∧
      let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre)
      let nextFree := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre + (fields.length + 1))
      memoryRel conf be (next + 1) refs (space - (fields.length + 1))
        (store.updateEq (.nextFree, .word nextFree))
        (storeEachMemory base 0 (.word header :: fields.map Prod.snd) memory) domain
        (((.block next tag (fields.map Prod.fst)),
          wordAddr conf (.pointer (heapLength pre) (.word (ptrBits conf tag fields.length)))) :: fields ++ vars) := by
  obtain ⟨addresses, lengthEq, projected, wordInv⟩ :=
    wordMlInv_allocateBlock conf fields vars refs pre post sp sp1 next tag limit be gens nonempty enough inv
  have wordsEq : addresses.map (wordAddr conf) = fields.map Prod.snd := by
    have mapped : List.Forall₂ (· = ·) (addresses.map (wordAddr conf)) (fields.map Prod.snd) :=
      List.forall₂_map_left_iff.mpr projected
    simpa only [List.forall₂_eq_eq_eq] using mapped
  have encoded' : encodeHeader conf (4 * tag) addresses.length = some header := by simpa [lengthEq] using encoded
  obtain ⟨curr, currStore, nextStore, updatedHeap⟩ := heapInMemoryStore_storeConstructor_of_encoded conf pre post addresses tag sp sp1
    header gens store memory domain limit (by omega) encoded' heapMem
  refine ⟨curr, addresses, currStore, nextStore, lengthEq, wordsEq, ?_⟩
  dsimp only
  refine ⟨pre ++ [blockRep tag addresses] ++ heapExpand (sp + sp1 - (addresses.length + 1)) ++ post,
    limit, heapLength pre + (addresses.length + 1), sp - (addresses.length + 1), sp1, gens,
    ?_, ?_, limitBound, ?_⟩
  · simpa [lengthEq, wordsEq] using updatedHeap
  · simpa [lengthEq] using wordInv
  · omega

/-- A related nonempty constructor field list with enough reserved space has
the complete post-allocation memory relation. The free-region decomposition
and available heap space are derived from the original relation. -/
theorem memoryRel_allocateBlock {width : Nat} [NeZero width] (conf : Config)
    (fields vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (next tag space : Nat) (be : Bool) (header : BitVec width)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (nonempty : fields ≠ []) (enough : fields.length + 1 ≤ space)
    (encoded : encodeHeader conf (4 * tag) fields.length = some header)
    (related : memoryRel conf be next refs space store memory domain (fields ++ vars)) :
    ∃ (curr : BitVec width) (index : Nat),
      store.lookup .currHeap = some (.word curr) ∧
      store.lookup .nextFree = some (.word (curr + StackRemove.bytesInWord width * BitVec.ofNat width index)) ∧
      let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width index
      let nextFree := curr + StackRemove.bytesInWord width * BitVec.ofNat width (index + (fields.length + 1))
      memoryRel conf be (next + 1) refs (space - (fields.length + 1))
        (store.updateEq (.nextFree, .word nextFree))
        (storeEachMemory base 0 (.word header :: fields.map Prod.snd) memory) domain
        (((.block next tag (fields.map Prod.fst)),
          wordAddr conf (.pointer index (.word (ptrBits conf tag fields.length)))) :: fields ++ vars) := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, limitBound, spaceBound⟩ := related
  have invariant := wordInv
  obtain ⟨roots, absInv, _⟩ := wordInv
  obtain ⟨_, _, _, unused, _⟩ := absInv
  have positive : sp + sp1 ≠ 0 := by omega
  have found : heapLookup a heap = some (.unused (sp + sp1 - 1)) := unused.1 positive
  obtain ⟨pre, post, heapEq, indexEq⟩ := heapLookup_split heap a _ found
  have freeEq : (heapExpand (sp + sp1) : ValueHeap width) = [.unused (sp + sp1 - 1)] := by
    unfold heapExpand
    rw [ite_eq_right positive]
  have shape : heap = pre ++ heapExpand (sp + sp1) ++ post := by
    simpa only [freeEq, List.append_assoc, List.singleton_append] using heapEq
  subst heap
  subst a
  have heapMem' : heapInMemoryStore (pre ++ heapExpand (sp + sp1) ++ post)
      (heapLength pre) sp sp1 gens conf store memory domain limit := by
    simpa only [freeEq, List.append_assoc, List.singleton_append] using heapMem
  have invariant' : wordMlInv (pre ++ heapExpand (sp + sp1) ++ post, be, heapLength pre, sp, sp1, gens)
      limit next conf refs (fields ++ vars) := by
    simpa only [freeEq, List.append_assoc, List.singleton_append] using invariant
  obtain ⟨curr, _, currStore, nextStore, _, _, result⟩ := memoryRel_allocateBlock_from_heap conf fields vars refs pre post
    sp sp1 next tag limit space be gens header store memory domain nonempty (by omega) spaceBound limitBound encoded heapMem' invariant'
  exact ⟨curr, heapLength pre, currStore, nextStore, result⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Correct

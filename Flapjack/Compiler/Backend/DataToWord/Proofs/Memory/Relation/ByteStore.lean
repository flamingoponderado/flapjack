import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteLoad
import Flapjack.Compiler.Backend.LabToTarget.InstMem
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Heap
import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdateStack

/-! Concrete writes to a separated packed byte payload. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.HolByte

/-- Exchange the first two separated assertions while retaining the frame. -/
theorem star_swap_first {α : Type} (p q r : (α → Prop) → Prop) :
    SetSep.star p (SetSep.star q r) = SetSep.star q (SetSep.star p r) := by
  rw [SetSep.starAssoc, SetSep.starComm p q, ← SetSep.starAssoc]

/-- Writing one element of a separated word list updates exactly its graph
entry and preserves the entire external separation frame. -/
theorem wordList_write {width : Nat} [NeZero width] {β : Type}
    (address : BitVec width) (values : List β) (i : Nat) (newValue : β)
    (memory : BitVec width → β) (domain : BitVec width → Prop)
    (frame : ((BitVec width × β) → Prop) → Prop) (bound : i < values.length)
    (separated : SetSep.star (Misc.wordList address values) frame (SetSep.fun2Set (memory, domain))) :
    SetSep.star (Misc.wordList address (values.set i newValue)) frame
      (SetSep.fun2Set ((fun key => if key = address + BitVec.ofNat width i * StackRemove.bytesInWord width
        then newValue else memory key), domain)) := by
  classical
  induction values generalizing address i frame with
  | nil => simp at bound
  | cons value values ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, Misc.wordList, ← SetSep.starAssoc] at separated ⊢
      have changed := SetSep.writeFun2Set newValue address value _ memory domain separated
      rw [SetSep.starComm] at changed
      convert changed using 2
      congr 1
      funext key
      by_cases h : key = address <;> simp [h]
    | succ i =>
      simp only [List.set_cons_succ, Misc.wordList, ← SetSep.starAssoc] at separated ⊢
      rw [star_swap_first] at separated
      have changed := ih (address + StackRemove.bytesInWord width) i
        (SetSep.star (SetSep.one (address, value)) frame) (by simpa using bound) separated
      rw [star_swap_first] at changed
      have addressEq : (address + StackRemove.bytesInWord width) +
          BitVec.ofNat width i * StackRemove.bytesInWord width =
          address + BitVec.ofNat width (i + 1) * StackRemove.bytesInWord width := by
        simp only [BitVec.ofNat_add, BitVec.add_mul, BitVec.one_mul]
        ac_rfl
      simpa only [addressEq] using changed

/-- Updating a source byte updates the corresponding packed 64-bit word in
the concrete memory graph, while preserving the whole separation frame. -/
theorem bytePayload_store64 (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (base : BitVec 64) (be : Bool) (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Prop)
    (frame : ((BitVec 64 × WordLocW 64) → Prop) → Prop) (i : Nat) (byte : BitVec 8)
    (indexBound : i < bytes.length) (capacity : bytes.length ≤ words.length * 8)
    (separated : SetSep.star (Misc.wordList base ((DataToWord.writeBytes bytes words be).map WordLocW.word)) frame
      (SetSep.fun2Set (memory, domain))) :
    ∃ oldWord, memory (base + BitVec.ofNat 64 (i / 8) * 8) = .word oldWord ∧
      SetSep.star (Misc.wordList base ((DataToWord.writeBytes (bytes.set i byte) words be).map WordLocW.word)) frame
        (SetSep.fun2Set ((fun key => if key = base + BitVec.ofNat 64 (i / 8) * 8 then
          .word (setByte (BitVec.ofNat 64 (i % 8)) byte oldWord be) else memory key), domain)) := by
  let packed := DataToWord.writeBytes bytes words be
  have length : packed.length = words.length := writeBytes_wordCount bytes words be
  have bound : i / 8 < packed.length := by
    rw [length]
    exact (Nat.div_lt_iff_lt_mul (by decide)).2 (by omega)
  let oldWord := packed[i / 8]
  have graph : SetSep.fun2Set (memory, domain) (base + BitVec.ofNat 64 (i / 8) * 8, .word oldWord) := by
    rcases separated with ⟨left, right, partition, payload, rest⟩
    rw [← partition.1]
    apply Or.inl
    have entry := wordList_indexMember (packed.map WordLocW.word) (i / 8) (by simpa using bound) base left payload
    simpa [StackRemove.bytesInWord, oldWord] using entry
  have memEq := ((SetSep.fun2SetThm memory domain _ _).mp graph).1
  refine ⟨oldWord, memEq, ?_⟩
  have write := wordList_write base (packed.map WordLocW.word) (i / 8)
    (.word (setByte (BitVec.ofNat 64 (i % 8)) byte oldWord be)) memory domain frame (by simpa using bound) separated
  have listEq : (DataToWord.writeBytes (bytes.set i byte) words be).map WordLocW.word =
      (packed.map WordLocW.word).set (i / 8) (.word (setByte (BitVec.ofNat 64 (i % 8)) byte oldWord be)) := by
    rw [writeBytes_setByte64 bytes words be i byte indexBound capacity]
    rw [List.modify_eq_set_get _ bound]
    simp [packed, oldWord, List.map_set]
  rw [listEq]
  simp only [StackRemove.bytesInWord] at write
  convert write using 2
  congr 1

/-- The actual 64-bit word-semantics byte store succeeds and preserves the
separated packed-payload assertion for the source list update. -/
theorem bytePayload_memStore64 (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (base : BitVec 64) (be : Bool) (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (frame : ((BitVec 64 × WordLocW 64) → Prop) → Prop) (i : Nat) (byte : BitVec 8)
    (aligned : (base >>> (3 : Nat)) <<< (3 : Nat) = base) (indexBound : i < bytes.length)
    (wordBound : i < 2 ^ 64) (capacity : bytes.length ≤ words.length * 8)
    (separated : SetSep.star (Misc.wordList base ((DataToWord.writeBytes bytes words be).map WordLocW.word)) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    ∃ updated, memStoreByteAuxExact memory domain be (base + BitVec.ofNat 64 i) byte = some updated ∧
      SetSep.star (Misc.wordList base ((DataToWord.writeBytes (bytes.set i byte) words be).map WordLocW.word)) frame
        (SetSep.fun2Set (updated, fun addr => domain addr = true)) := by
  obtain ⟨oldWord, memEq, assertion⟩ := bytePayload_store64 bytes words base be memory
    (fun addr => domain addr = true) frame i byte indexBound capacity separated
  have remainder : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have small : (BitVec.ofNat 64 (i % 8)).ult 8 = true := by
    simp only [BitVec.ult_eq_decide, decide_eq_true_eq, BitVec.toNat_ofNat]
    norm_num
    rw [Nat.mod_eq_of_lt (by omega : i % 8 < 18446744073709551616)]
    exact remainder
  have decomposition : BitVec.ofNat 64 i = BitVec.ofNat 64 (i / 8) * 8 + BitVec.ofNat 64 (i % 8) := by
    have h := Nat.mod_add_div i 8
    have eq : i = i / 8 * 8 + i % 8 := by omega
    conv_lhs => rw [eq]
    simp only [BitVec.ofNat_add, BitVec.ofNat_mul]
    rfl
  have alignEq : riscvByteAlignHOL (base + BitVec.ofNat 64 i) = base + BitVec.ofNat 64 (i / 8) * 8 := by
    rw [decomposition, ← BitVec.add_assoc]
    exact alignedByteAddress64 base (BitVec.ofNat 64 (i / 8)) (BitVec.ofNat 64 (i % 8)) aligned small
  have baseMod : base.toNat % 8 = 0 := by
    have aligned3 : holAligned 3 base = true := by simp [holAligned, holAlign_eq_shift, aligned]
    simpa using (holAligned_iff 3 base).mp aligned3
  have addressMod : (base + BitVec.ofNat 64 i).toNat % 8 = i % 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound]
    norm_num
    omega
  have remNat : (BitVec.ofNat 64 (i % 8)).toNat = i % 8 := by
    simp only [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    norm_num
    omega
  have byteEq : setByteHOL8 (base + BitVec.ofNat 64 i) byte oldWord be =
      setByte (BitVec.ofNat 64 (i % 8)) byte oldWord be := by
    rw [LabToTarget.setByteHOL8_eq]
    simp only [setByte, byteIndex, show 64 / 8 = 8 by decide,
      addressMod, remNat, Nat.mod_eq_of_lt remainder]
  have loaded := bytePayload_load64 bytes words base be memory domain frame i aligned indexBound wordBound capacity separated
  have inDomain : domain (base + BitVec.ofNat 64 (i / 8) * 8) = true := by
    unfold memLoadByteAuxExact at loaded
    rw [alignEq, memEq] at loaded
    simp at loaded
    exact loaded.1
  refine ⟨_, ?_, assertion⟩
  unfold memStoreByteAuxExact
  simp only [alignEq, memEq, inDomain, ↓reduceIte, byteEq]

/-- Updating one byte of a concrete byte-cell assertion preserves its header,
side conditions, and any disjoint surrounding heap frame. -/
theorem wordEl_byteStore64 (conf : DataToWord.Config) (be flag : Bool)
    (bytes : List (BitVec 8)) (words : List (BitVec 64)) (base : BitVec 64)
    (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (frame : ((BitVec 64 × WordLocW 64) → Prop) → Prop) (i : Nat) (byte : BitVec 8)
    (aligned : ((base + 8) >>> (3 : Nat)) <<< (3 : Nat) = base + 8)
    (indexBound : i < bytes.length) (wordBound : i < 2 ^ 64)
    (capacity : bytes.length ≤ words.length * 8)
    (separated : SetSep.star (wordEl base (bytesRep be flag bytes words) conf) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    ∃ updated, memStoreByteAuxExact memory domain be (base + 8 + BitVec.ofNat 64 i) byte = some updated ∧
      SetSep.star (wordEl base (bytesRep be flag (bytes.set i byte) words) conf) frame
        (SetSep.fun2Set (updated, fun addr => domain addr = true)) := by
  simp only [wordEl, bytesRep, wordPayload, List.isEmpty_nil, Bool.true_and,
    List.length_map, writeBytes_wordCount, Misc.wordList, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  obtain ⟨updated, store, result⟩ := bytePayload_memStore64 bytes words (base + 8) be memory domain _ i byte
    aligned indexBound wordBound capacity (by simpa [StackRemove.bytesInWord] using separated)
  refine ⟨updated, store, ?_⟩
  rw [star_swap_first] at result
  simpa [wordEl, bytesRep, wordPayload, writeBytes_wordCount, Misc.wordList, ← SetSep.starAssoc,
    StackRemove.bytesInWord] using result

/-- The concrete store preserves a whole word heap around the updated byte
cell, including an arbitrary disjoint frame such as the alternate heap. -/
theorem wordHeap_byteStore64 (conf : DataToWord.Config) (be flag : Bool)
    (bytes : List (BitVec 8)) (words : List (BitVec 64)) (curr : BitVec 64)
    (pre post : ValueHeap 64) (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (frame : ((BitVec 64 × WordLocW 64) → Prop) → Prop) (i : Nat) (byte : BitVec 8)
    (aligned : ((curr + 8 * BitVec.ofNat 64 (heapLength pre) + 8) >>> (3 : Nat)) <<< (3 : Nat) =
      curr + 8 * BitVec.ofNat 64 (heapLength pre) + 8)
    (indexBound : i < bytes.length) (wordBound : i < 2 ^ 64)
    (capacity : bytes.length ≤ words.length * 8)
    (separated : SetSep.star (wordHeap curr (pre ++ [bytesRep be flag bytes words] ++ post) conf) frame
      (SetSep.fun2Set (memory, fun addr => domain addr = true))) :
    ∃ updated, memStoreByteAuxExact memory domain be
      (curr + 8 * BitVec.ofNat 64 (heapLength pre) + 8 + BitVec.ofNat 64 i) byte = some updated ∧
      SetSep.star (wordHeap curr (pre ++ [bytesRep be flag (bytes.set i byte) words] ++ post) conf) frame
        (SetSep.fun2Set (updated, fun addr => domain addr = true)) := by
  have sameLength := (bytesRep_shape be flag bytes (bytes.set i byte) words).length
  rw [List.append_assoc, wordHeapAppend] at separated
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  obtain ⟨updated, store, result⟩ := wordEl_byteStore64 conf be flag bytes words
    (curr + 8 * BitVec.ofNat 64 (heapLength pre)) memory domain _ i byte aligned indexBound wordBound capacity
    (by simpa [StackRemove.bytesInWord] using separated)
  refine ⟨updated, store, ?_⟩
  rw [star_swap_first] at result
  rw [List.append_assoc, wordHeapAppend]
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc]
  simpa [StackRemove.bytesInWord, ← sameLength] using result

/-- The word heap and its alternate heap continue to satisfy the concrete
heap/store invariant after a bounded byte store. The caller supplies the
byte payload capacity established from the encoded byte-cell header. -/
theorem heapInMemoryStore_byteStore64 (conf : DataToWord.Config) (be flag : Bool)
    (bytes : List (BitVec 8)) (words : List (BitVec 64)) (pre post : ValueHeap 64)
    (a sp sp1 : Nat) (gens : GcCombined.GenState) (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool) (limit i : Nat) (byte : BitVec 8)
    (indexBound : i < bytes.length) (wordBound : i < 2 ^ 64)
    (capacity : bytes.length ≤ words.length * 8)
    (heapMem : heapInMemoryStore (pre ++ [bytesRep be flag bytes words] ++ post)
      a sp sp1 gens conf store memory domain limit) :
    ∃ curr updated, store.lookup .currHeap = some (.word curr) ∧
      memStoreByteAuxExact memory domain be
        (curr + 8 * BitVec.ofNat 64 (heapLength pre) + 8 + BitVec.ofNat 64 i) byte = some updated ∧
      heapInMemoryStore (pre ++ [bytesRep be flag (bytes.set i byte) words] ++ post)
        a sp sp1 gens conf store updated domain limit := by
  obtain ⟨bound1, bound2, shift, lenNonzero, lenBound, shiftBound, globals,
    curr, other, currAligned, otherAligned, currStore, otherStore, nextStore,
    triggerStore, endStore, lengthStore, globInv, genInv, separated⟩ := heapMem
  have currAligned3 : (curr >>> (3 : Nat)) <<< (3 : Nat) = curr := by
    simpa [holByteAligned, holAligned, holLOG2_eq_log2 (n := 8) (by decide), holAlign_eq_shift] using currAligned
  have targetAligned : ((curr + 8 * BitVec.ofNat 64 (heapLength pre) + 8) >>> (3 : Nat)) <<< (3 : Nat) =
      curr + 8 * BitVec.ofNat 64 (heapLength pre) + 8 := by
    bv_decide
  obtain ⟨updated, memWrite, heapNew⟩ := wordHeap_byteStore64 conf be flag bytes words curr pre post
    memory domain _ i byte targetAligned indexBound wordBound capacity separated
  have lengthEq := heapLength_shape (byteHeap_shape be flag bytes (bytes.set i byte) words pre post)
  refine ⟨curr, updated, currStore, memWrite, ?_⟩
  refine ⟨?_, ?_, shift, lenNonzero, lenBound, shiftBound, globals, curr, other, currAligned, otherAligned,
    currStore, otherStore, nextStore, triggerStore, endStore, lengthStore, globInv, genInv, heapNew⟩
  · simpa only [← lengthEq] using bound1
  · simpa only [← lengthEq] using bound2

/-- The abstract byte-array allocation size and the heap-store bound imply
both payload capacity and the 64-bit bound on any valid byte index. -/
theorem byteHeap_storeBounds64 (conf : DataToWord.Config) (be flag : Bool)
    (bytes : List (BitVec 8)) (words : List (BitVec 64)) (pre post : ValueHeap 64)
    (a sp sp1 : Nat) (gens : GcCombined.GenState) (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool) (limit i : Nat)
    (count : words.length = bytes.length / 8 + 1) (indexBound : i < bytes.length)
    (heapMem : heapInMemoryStore (pre ++ [bytesRep be flag bytes words] ++ post)
      a sp sp1 gens conf store memory domain limit) :
    bytes.length ≤ words.length * 8 ∧ i < 2 ^ 64 := by
  have division := Nat.mod_add_div bytes.length 8
  have remBound := Nat.mod_lt bytes.length (by decide : 0 < 8)
  have capacity : bytes.length ≤ words.length * 8 := by omega
  have sizeBound : words.length ≤ heapLength (pre ++ [bytesRep be flag bytes words] ++ post) := by
    rw [List.append_assoc, heapLength_append]
    simp only [List.singleton_append]
    change words.length ≤ heapLength pre + (elLength (bytesRep be flag bytes words) + heapLength post)
    simp only [bytesRep, writeBytes_wordCount, elLength]
    omega
  simp only [List.append_assoc, List.singleton_append] at sizeBound
  have heapBound := heapMem.2.1
  norm_num at heapBound ⊢
  constructor
  · exact capacity
  · omega

/-- A source byte-array update and the matching concrete 64-bit byte store
preserve the full data-to-word memory relation. The address is expressed via
the heap prefix exposed by the abstract byte-update theorem. -/
theorem memoryRel_byteStore64 (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (bit flag : Bool) (ptr : Nat) (bytes : List (BitVec 8)) (root : WordLocW 64)
    (vars : List (DataSem.Value × WordLocW 64)) (i : Nat) (byte : BitVec 8)
    (found : sptLookup ptr refs = some (.byteArray flag bytes)) (indexBound : i < bytes.length)
    (related : memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, root) :: vars)) :
    ∃ (curr : BitVec 64) (pre : ValueHeap 64) (updated : BitVec 64 → WordLocW 64) (w : BitVec 64),
      root = .word w ∧ getRealAddr conf store w = some (curr + 8 * BitVec.ofNat 64 (heapLength pre)) ∧
      store.lookup .currHeap = some (.word curr) ∧ memStoreByteAuxExact memory domain be
        (curr + 8 * BitVec.ofNat 64 (heapLength pre) + 8 + BitVec.ofNat 64 i) byte = some updated ∧
      memoryRel conf be next (sptInsert ptr (.byteArray flag (bytes.set i byte)) refs)
        space store updated domain ((.refPtr bit ptr, root) :: vars) := by
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, wordInv, bound, spaceBound⟩ := related
  obtain ⟨roots, absInv, rootWords⟩ := wordInv
  have absInv' : absMlInv conf (.refPtr bit ptr :: vars.map Prod.fst) refs
      (roots, heap, be, a, sp, sp1, gens) limit next := by simpa using absInv
  obtain ⟨roots2, pre, post, words, rootsEq, heapEq, wordCount, absUpdated⟩ :=
    updateByteRef conf bit ptr (vars.map Prod.fst) refs roots heap be a sp sp1 gens limit next flag bytes
      (bytes.set i byte) ⟨absInv', found, by simp⟩
  rw [heapEq] at heapMem
  have count : words.length = bytes.length / 8 + 1 := by simpa using wordCount
  obtain ⟨capacity, wordBound⟩ := byteHeap_storeBounds64 conf be flag bytes words pre post
    a sp sp1 gens store memory domain limit i count indexBound heapMem
  obtain ⟨curr, updated, currStore, memWrite, heapUpdated⟩ :=
    heapInMemoryStore_byteStore64 conf be flag bytes words pre post a sp sp1 gens store memory domain limit i byte
      indexBound wordBound capacity heapMem
  have projected : wordAddr conf (.pointer (heapLength pre) (.word 0)) = root := by
    rw [rootsEq] at rootWords
    cases rootWords with
    | cons head _ => exact head
  have rootEq : root = .word (getAddr conf (heapLength pre) (.word 0)) := by
    simpa [wordAddr] using projected.symm
  have cell := heapLookup_byteHeap_here pre post be flag bytes words
  have real := (getRealAddr_getAddr conf store _ (heapLength pre) _ curr (.word 0)
    ⟨heapMem.1, cell, currStore, Or.inr rfl⟩).2
  refine ⟨curr, pre, updated, getAddr conf (heapLength pre) (.word 0), rootEq, ?_, currStore, memWrite, ?_⟩
  · simpa [StackRemove.bytesInWord, BitVec.mul_comm] using real
  refine ⟨pre ++ [bytesRep be flag (bytes.set i byte) words] ++ post, limit, a, sp, sp1, gens,
    heapUpdated, ?_, bound, spaceBound⟩
  refine ⟨roots, ?_, rootWords⟩
  simpa using absUpdated

/-- The related reference supplies the actual byte-store address computed by
the compiler, and the resulting memory remains related to the updated source
references. This is the 64-bit store component of the byte-array memory theorem. -/
theorem memoryRel_byteStoreAddress64 (conf : DataToWord.Config) (be : Bool) (next : Nat)
    (refs : Spt (BvlSem.Ref DataSem.Value)) (space : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (memory : BitVec 64 → WordLocW 64) (domain : BitVec 64 → Bool)
    (bit flag : Bool) (ptr : Nat) (bytes : List (BitVec 8)) (root : WordLocW 64)
    (vars : List (DataSem.Value × WordLocW 64)) (i : Nat) (byte : BitVec 8)
    (found : sptLookup ptr refs = some (.byteArray flag bytes)) (indexBound : i < bytes.length)
    (related : memoryRel conf be next refs space store memory domain ((.refPtr bit ptr, root) :: vars)) :
    ∃ w address updated, root = .word w ∧ getRealAddr conf store w = some address ∧
      memStoreByteAuxExact memory domain be (address + 8 + BitVec.ofNat 64 i) byte = some updated ∧
      memoryRel conf be next (sptInsert ptr (.byteArray flag (bytes.set i byte)) refs)
        space store updated domain ((.refPtr bit ptr, root) :: vars) := by
  obtain ⟨curr, pre, updated, w, rootEq, address, _, stored, result⟩ :=
    memoryRel_byteStore64 conf be next refs space store memory domain bit flag ptr bytes root vars i byte
      found indexBound related
  exact ⟨w, curr + 8 * BitVec.ofNat 64 (heapLength pre), updated, rootEq, address, stored, result⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

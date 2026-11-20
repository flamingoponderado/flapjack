module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteHeapStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteHeaderDecode
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteAlignment
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.GenerationalStore

@[expose] public section

/-! Byte-array updates in the original heap/store memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.HolByte

private theorem wordEl_byteCapacity {width : Nat} [NeZero width] (conf : Config) (bytes : List (BitVec 8)) (words : List (BitVec width))
    (be flag : Bool) (good : goodDimindex width) (config : conf.lenSize + 7 < width)
    (base : BitVec width) (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (whole : (BitVec width × WordLocW width) → Prop)
    (separated : SetSep.star (wordEl base (bytesRep be flag bytes words) conf) frame whole) :
    bytes.length ≤ words.length * (width / 8) := by
  simp only [wordEl, bytesRep, wordPayload, List.isEmpty_nil, Bool.true_and, List.length_map,
    writeBytes_wordCount, decide_eq_true_eq] at separated
  obtain ⟨_, _, _, ⟨_, _, _, _, pure⟩, _⟩ := separated
  have facts := pure.2
  have wordBound : words.length < 2 ^ width :=
    Nat.lt_of_lt_of_le facts.1 (Nat.pow_le_pow_right (by decide) (by omega))
  have decoded : (WordGcFunctions.decodeLength conf (makeByteHeader conf flag bytes.length) : BitVec width).toNat = words.length := by
    rw [facts.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wordBound]
  have lengthBound : bytes.length + 2 ^ wordShiftAmount width < 2 ^ (conf.lenSize + wordShiftAmount width) := by
    simpa [wordShiftAmount] using facts.2.2.2
  have result := decodeLength_makeByteHeader (width := width) conf flag bytes.length ⟨good, config, lengthBound⟩
  simpa [decoded] using result.1

private theorem wordHeap_byteCapacity {width : Nat} [NeZero width] (conf : Config) (bytes : List (BitVec 8)) (words : List (BitVec width))
    (be flag : Bool) (good : goodDimindex width) (config : conf.lenSize + 7 < width)
    (curr : BitVec width) (pre post : ValueHeap width)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (whole : (BitVec width × WordLocW width) → Prop)
    (separated : SetSep.star (wordHeap curr (pre ++ [bytesRep be flag bytes words] ++ post) conf) frame whole) :
    bytes.length ≤ words.length * (width / 8) := by
  rw [List.append_assoc, wordHeapAppend] at separated
  simp only [List.singleton_append, wordHeap, ← SetSep.starAssoc] at separated
  rw [star_swap_first] at separated
  exact wordEl_byteCapacity conf bytes words be flag good config _ _ whole separated

open Flapjack.Compiler.Backend.GcCombined
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "heap_in_memory_store_UpdateByte"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem heapInMemoryStore_updateByte {width : Nat} [NeZero width] (heap pre post : ValueHeap width)
    (a sp sp1 : Nat) (gens : GenState) (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (memory : BitVec width → WordLocW width)
    (domain : BitVec width → Bool) (limit : Nat) (be flag : Bool) (bytes : List (BitVec 8))
    (words : List (BitVec width)) (i : Nat) (ad curr w : BitVec width) (byte : BitVec 8) :
    heapInMemoryStore heap a sp sp1 gens conf store memory domain limit ∧
    heap = pre ++ [bytesRep be flag bytes words] ++ post ∧ i < bytes.length ∧
    ad = curr + StackRemove.bytesInWord width + BitVec.ofNat width i +
      StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) ∧
    store.lookup .currHeap = some (.word curr) ∧ memory (holByteAlign ad) = .word w ∧
    goodDimindex width →
    heapInMemoryStore (pre ++ [bytesRep be flag (bytes.set i byte) words] ++ post)
      a sp sp1 gens conf store
      (fun key => if key = holByteAlign ad then .word (setByte ad byte w be) else memory key) domain limit := by
  rintro ⟨heapMem, rfl, inBytes, adEq, currLookup, memRead, good⟩
  obtain ⟨bound1, bound2, shift, lenNonzero, lenBound, shiftBound, globals,
    cur, other, curAligned, otherAligned, curStore, otherStore, nextStore,
    triggerStore, endStore, lengthStore, globInv, genInv, separated⟩ := heapMem
  have currEq : cur = curr := by
    rw [currLookup] at curStore
    cases curStore
    rfl
  subst cur
  let bw := width / 8
  have bwPos : 0 < bw := by rcases good with rfl | rfl <;> decide
  let j := i / bw
  let r := i % bw
  have rbound : r < width / 8 := Nat.mod_lt i bwPos
  have decom : j * (width / 8) + r = i := by simpa [j, r, bw, Nat.mul_comm] using Nat.div_add_mod i bw
  have capacity := wordHeap_byteCapacity conf bytes words be flag good lenBound curr pre post _ _ separated
  have jbound : j < words.length := by
    dsimp [j, bw] at *
    rcases good with h | h <;> subst width <;> norm_num at * <;> omega
  have changed := wordHeap_byteStore conf bytes words be flag j r byte good rbound (by simpa [decom] using inBytes)
    jbound curr pre post memory (fun addr => domain addr = true) _ separated
  let base := curr + StackRemove.bytesInWord width * BitVec.ofNat width (heapLength pre) +
    StackRemove.bytesInWord width + BitVec.ofNat width j * StackRemove.bytesInWord width
  have adBase : ad = base + BitVec.ofNat width r := by
    rw [adEq, ← decom]
    dsimp [base, StackRemove.bytesInWord]
    simp only [BitVec.ofNat_add, BitVec.ofNat_mul]
    ac_rfl
  have currMod := (Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.byteAligned_iff_divisible curr good).mp curAligned
  have baseMod : base.toNat % (width / 8) = 0 := by
    rcases good with h | h <;> subst width <;>
      norm_num [base, StackRemove.bytesInWord, BitVec.toNat_add, BitVec.toNat_mul,
        BitVec.toNat_ofNat, Nat.mod_mod_of_dvd, Nat.add_mod, Nat.mul_mod] at * <;> assumption
  have baseAlign : holByteAlign ad = base := by
    rw [adBase]
    exact Flapjack.Compiler.Backend.LabToTarget.holByteAlign_aligned_add good base baseMod r rbound
  have baseFixed : holByteAlign base = base := by
    simpa using Flapjack.Compiler.Backend.LabToTarget.holByteAlign_aligned_add good base baseMod 0 (by omega)
  dsimp only at changed
  obtain ⟨read, _, result⟩ := changed
  have readAtBase : memory base = .word w := by simpa [baseAlign] using memRead
  have readEq : w = (writeBytes bytes words be)[j]'(by simpa [writeBytes_wordCount] using jbound) := by
    apply WordLocW.word.inj
    exact readAtBase.symm.trans read
  have byteEq : setByte ad byte w be = setByte (BitVec.ofNat width r) byte w be := by
    apply setByte_changeAddress
    rw [adBase, BitVec.add_comm, ← baseFixed]
    exact toNat_add_byteAlign base (BitVec.ofNat width r) good
  have lengthEq : heapLength (pre ++ [bytesRep be flag bytes words] ++ post) =
      heapLength (pre ++ [bytesRep be flag (bytes.set i byte) words] ++ post) := by
    simp [heapLength, List.map_append, List.sum_append, bytesRep, elLength, writeBytes_wordCount]
  refine ⟨?_, ?_, shift, lenNonzero, lenBound, shiftBound, globals, curr, other, curAligned, otherAligned,
    curStore, otherStore, nextStore, triggerStore, endStore, lengthStore, globInv, genInv, ?_⟩
  · rw [← lengthEq]
    exact bound1
  · rw [← lengthEq]
    exact bound2
  · rw [← decom]
    change SetSep.star (wordHeap curr (pre ++ [bytesRep be flag (bytes.set (j * (width / 8) + r) byte) words] ++ post) conf)
      (wordHeap other (heapExpand limit) conf)
      (SetSep.fun2Set ((fun key => if key = base then .word (setByte (BitVec.ofNat width r) byte
        ((writeBytes bytes words be)[j]'(by simpa [writeBytes_wordCount] using jbound)) be) else memory key),
        fun addr => domain addr = true)) at result
    rw [← readEq, ← byteEq, ← baseAlign] at result
    exact result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

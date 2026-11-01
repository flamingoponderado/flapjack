import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store

/-! Concrete addresses and offsets for the data-to-word memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- The lookup-and-support view of the source finite store map. -/
structure MemoryStoreBroad (width : Nat) [NeZero width] where
  lookup : WordStoreHOL → Option (WordLocW width)
  finiteSupport : ∃ keys : List WordStoreHOL, ∀ key, lookup key ≠ none → key ∈ keys

namespace MemoryStoreBroad

/-- Forget the finite-map wrapper while retaining its lookup and support. -/
def toBroad {width : Nat} [NeZero width] (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) : MemoryStoreBroad width :=
  ⟨store.lookup, store.finiteSupport⟩

/-- Reconstruct the canonical finite-map carrier. -/
def ofBroad {width : Nat} [NeZero width] (store : MemoryStoreBroad width) : HolFiniteMapExact WordStoreHOL (WordLocW width) :=
  ⟨store.lookup, store.finiteSupport⟩

end MemoryStoreBroad

/-- The real-address operation's finite store parameter has a lossless codec. -/
theorem holFmapAsFiniteSupportParamWitness_getRealAddr_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).lookup key = store.lookup key ∧
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
    MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store) = store := by
  cases store
  exact ⟨rfl, rfl, rfl⟩

/-- Recover the machine address corresponding to an encoded heap pointer. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_real_addr_def"
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
def getRealAddr {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (w : BitVec width) : Option (BitVec width) :=
  let k := wordShiftAmount width
  match store.lookup .currHeap with
  | some (.word curr) =>
      if k = shiftLength conf ∧ conf.lenBits = 0 ∧ conf.tagBits = 0 then
        some (curr + w - 1)
      else if k ≤ conf.padBits + 1 then
        some (curr + (w >>> (shiftLength conf - k)))
      else some (curr + ((w >>> shiftLength conf) <<< k))
  | _ => none

/-- Recover the address offset of a tagged integer used as a field index. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_real_offset_def"
  (words_as_type_indexed_bitvec)]
def getRealOffset {width : Nat} [NeZero width] (w : BitVec width) : Option (BitVec width) :=
  if width = 32 then some (w + StackRemove.bytesInWord width)
  else some ((w <<< 1) + StackRemove.bytesInWord width)

/-- The simple-address operation's finite store parameter has a lossless codec. -/
theorem holFmapAsFiniteSupportParamWitness_getRealSimpleAddr_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).lookup key = store.lookup key ∧
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
    MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store) = store := by
  cases store
  exact ⟨rfl, rfl, rfl⟩

/-- Recover a machine address using the original simple shift formula. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_real_simple_addr_def"
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
def getRealSimpleAddr {width : Nat} [NeZero width] (conf : Config)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (w : BitVec width) : Option (BitVec width) :=
  match store.lookup .currHeap with
  | some (.word curr) => some (curr + ((w >>> shiftLength conf) <<< wordShiftAmount width))
  | _ => none

/-- The tagged encoding of an index gives the expected word-sized field offset. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_real_offset_thm"
  (words_as_type_indexed_bitvec)]
theorem getRealOffset_thm {width : Nat} [NeZero width] (index : Nat) :
    goodDimindex width →
    getRealOffset (BitVec.ofNat width (4 * index) : BitVec width) =
      some (StackRemove.bytesInWord width + BitVec.ofNat width index * StackRemove.bytesInWord width) := by
  intro good
  rcases good with h | h <;> subst width <;>
    simp [getRealOffset, StackRemove.bytesInWord, BitVec.ofNat_mul] <;> bv_decide

/-- Pointer tag bits vanish when shifted past the complete pointer field. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_lowerbits_LSL_shift_length"
  (words_as_type_indexed_bitvec)]
theorem getLowerBits_shiftLength {width : Nat} [NeZero width] (conf : Config) (v : WordLocW width) :
    getLowerBits conf v >>> shiftLength conf = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have bounds : smallShiftLength conf ≤ shiftLength conf := by simp [smallShiftLength, shiftLength]
  have positive : 0 < shiftLength conf := by simp [shiftLength]
  cases v with
  | word w =>
    simp only [getLowerBits, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
    simp only [Nat.zero_add]
    have h : ¬ shiftLength conf + i < smallShiftLength conf := by omega
    simp [h, Nat.ne_of_gt positive]
  | loc a b =>
    simp [getLowerBits, Nat.ne_of_gt positive]

/-- A bounded index survives shifting left and then right by the same amount.
This is Flapjack bit-vector infrastructure for address recovery. -/
theorem bounded_shift_roundtrip {width : Nat} [NeZero width] (n k : Nat)
    (hn : n * 2 ^ k < 2 ^ width) :
    (BitVec.ofNat width n <<< k) >>> k = BitVec.ofNat width n := by
  have nle : n ≤ n * 2 ^ k := Nat.le_mul_of_pos_right n (Nat.two_pow_pos k)
  have nlt : n < 2 ^ width := Nat.lt_of_le_of_lt nle hn
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt nlt, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn, Nat.shiftRight_eq_div_pow]
  exact Nat.mul_div_cancel n (Nat.two_pow_pos k)

/-- At supported widths the word-byte multiplier is the source word shift.
This is Flapjack bit-vector infrastructure for address recovery. -/
theorem shiftWordBytes {width : Nat} [NeZero width] (good : goodDimindex width) (n : BitVec width) :
    (n <<< wordShiftAmount width) = n * StackRemove.bytesInWord width := by
  rcases good with h | h <;> subst width <;> simp [wordShiftAmount, StackRemove.bytesInWord] <;> bv_decide

/-- A heap-bounded encoded pointer recovers the expected simple machine address.
This is the simple-address component of the original combined theorem; the
optimized address branches still require their own proof. -/
theorem getRealSimpleAddr_getAddr {width : Nat} [NeZero width] {α β : Type}
    (conf : Config) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (heap : List (HeapElement α β)) (index : Nat) (element : HeapElement α β)
    (curr : BitVec width) (v : WordLocW width)
    (heapBound : heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf)
    (found : heapLookup index heap = some element)
    (stored : store.lookup .currHeap = some (.word curr)) (good : goodDimindex width) :
    getRealSimpleAddr conf store (getAddr conf index v) =
      some (curr + BitVec.ofNat width index * StackRemove.bytesInWord width) := by
  have indexBound : index < heapLength heap := heapLookup_less heap index element found
  have below : index < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le indexBound heapBound
  have bounded : index * 2 ^ shiftLength conf < 2 ^ width := by
    calc
      index * 2 ^ shiftLength conf < (2 ^ width / 2 ^ shiftLength conf) * 2 ^ shiftLength conf :=
        Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)
      _ ≤ 2 ^ width := Nat.div_mul_le_self _ _
  simp only [getRealSimpleAddr, stored, getAddr, BitVec.ushiftRight_or_distrib,
    getLowerBits_shiftLength, bounded_shift_roundtrip index (shiftLength conf) bounded,
    shiftWordBytes good]
  simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

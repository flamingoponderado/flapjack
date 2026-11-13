module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Store
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BitLemmas

@[expose] public section

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
    simp [getRealOffset, StackRemove.bytesInWord, BitVec.ofNat_mul] <;> bv_omega

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
  rcases good with h | h <;> subst width <;> simp [wordShiftAmount, StackRemove.bytesInWord] <;> bv_omega

/-- A heap-bounded encoded pointer recovers the expected simple machine address.
This Flapjack helper is the simple-address component of the combined theorem. -/
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

/-- Shifting beyond both the tag field and marker bit clears the lower bits.
This is Flapjack infrastructure for optimized address recovery. -/
theorem getLowerBits_shiftBeyond {width : Nat} [NeZero width] (conf : Config) (v : WordLocW width) (k : Nat)
    (bound : smallShiftLength conf ≤ k) (pos : 0 < k) : getLowerBits conf v >>> k = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases v with
  | word w =>
    simp only [getLowerBits, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_or,
      BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
    simp only [Nat.zero_add]
    have h : ¬ k + i < smallShiftLength conf := by omega
    simp [h, Nat.ne_of_gt pos]
  | loc a b => simp [getLowerBits, Nat.ne_of_gt pos]

/-- With no length or tag fields, the lower pointer bits consist only of the
marker. This is Flapjack infrastructure for optimized address recovery. -/
theorem getLowerBits_marker {width : Nat} [NeZero width] (conf : Config) (v : WordLocW width)
    (len : conf.lenBits = 0) (tag : conf.tagBits = 0) : getLowerBits conf v = 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  cases v with
  | word w =>
    simp only [getLowerBits, smallShiftLength, len, tag, Nat.zero_add,
      BitVec.getLsbD_or, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb']
    by_cases zero : i = 0
    · subst i
      simp [hi]
    · have notlt : ¬ i < 1 := by omega
      simp [notlt]
  | loc a b => rfl

/-- A bounded left shift followed by a shorter right shift retains the
remaining shift. This is Flapjack bit-vector infrastructure. -/
theorem bounded_shift_partial {width : Nat} [NeZero width] (n s k : Nat) (ks : k ≤ s)
    (hn : n * 2 ^ s < 2 ^ width) :
    (BitVec.ofNat width n <<< s) >>> (s - k) = (BitVec.ofNat width n <<< k) := by
  have nle : n ≤ n * 2 ^ s := Nat.le_mul_of_pos_right n (Nat.two_pow_pos s)
  have nlt : n < 2 ^ width := Nat.lt_of_le_of_lt nle hn
  have smallPow : 2 ^ k ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) ks
  have hsmall : n * 2 ^ k < 2 ^ width := Nat.lt_of_le_of_lt (Nat.mul_le_mul_left n smallPow) hn
  have hp : 2 ^ s = 2 ^ k * 2 ^ (s - k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt nlt, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hsmall,
    Nat.shiftRight_eq_div_pow]
  rw [hp, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

/-- The marker bit cancels in the direct-address optimization at both source
word widths. This is Flapjack bit-vector infrastructure. -/
theorem pointerMarker_cancel {width : Nat} [NeZero width] (good : goodDimindex width) (n curr : BitVec width) :
    curr + ((n <<< wordShiftAmount width) ||| 1) - 1 = curr + (n <<< wordShiftAmount width) := by
  have shifted (k : Nat) (positive : 0 < k) : (n <<< k) &&& 1 = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft]
    have widthPositive : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
    cases i with
    | zero => simp [positive, widthPositive]
    | succ j => simp
  have positive : 0 < wordShiftAmount width := by
    rcases good with h | h <;> subst width <;> simp [wordShiftAmount]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ (shifted _ positive)]
  rw [← BitVec.add_assoc, BitVec.add_sub_cancel]

/-- The combined address theorem's store argument has the canonical
lookup-and-support roundtrip. -/
theorem holFmapAsFiniteSupportParamWitness_getRealAddr_getAddr_store {width : Nat} [NeZero width]
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width)) (key : WordStoreHOL) :
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).lookup key = store.lookup key ∧
    (MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store)).finiteSupport = store.finiteSupport ∧
    MemoryStoreBroad.ofBroad (MemoryStoreBroad.toBroad store) = store := by
  cases store
  exact ⟨rfl, rfl, rfl⟩

/-- Both source address decoders recover the same bounded heap location. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_real_addr_get_addr"
  (fmap_as_finite_support_parameters := [store]) (words_as_type_indexed_bitvec)]
theorem getRealAddr_getAddr {width : Nat} [NeZero width] {α β : Type}
    (conf : Config) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (heap : List (HeapElement α β)) (index : Nat) (element : HeapElement α β)
    (curr : BitVec width) (v : WordLocW width) :
    heapLength heap ≤ 2 ^ width / 2 ^ shiftLength conf ∧
      heapLookup index heap = some element ∧ store.lookup .currHeap = some (.word curr) ∧ goodDimindex width →
    getRealSimpleAddr conf store (getAddr conf index v) =
      some (curr + BitVec.ofNat width index * StackRemove.bytesInWord width) ∧
    getRealAddr conf store (getAddr conf index v) =
      some (curr + BitVec.ofNat width index * StackRemove.bytesInWord width) := by
  rintro ⟨heapBound, found, stored, good⟩
  refine ⟨getRealSimpleAddr_getAddr conf store heap index element curr v heapBound found stored good, ?_⟩
  have indexBound : index < heapLength heap := heapLookup_less heap index element found
  have below : index < 2 ^ width / 2 ^ shiftLength conf := Nat.lt_of_lt_of_le indexBound heapBound
  have bounded : index * 2 ^ shiftLength conf < 2 ^ width := by
    calc
      index * 2 ^ shiftLength conf < (2 ^ width / 2 ^ shiftLength conf) * 2 ^ shiftLength conf :=
        Nat.mul_lt_mul_of_pos_right below (Nat.two_pow_pos _)
      _ ≤ 2 ^ width := Nat.div_mul_le_self _ _
  by_cases fast : wordShiftAmount width = shiftLength conf ∧ conf.lenBits = 0 ∧ conf.tagBits = 0
  · simp only [getRealAddr, stored, ite_eq_left fast, getAddr,
      getLowerBits_marker conf v fast.2.1 fast.2.2]
    rw [← fast.1, pointerMarker_cancel good, shiftWordBytes good]
  · by_cases short : wordShiftAmount width ≤ conf.padBits + 1
    · have ks : wordShiftAmount width ≤ shiftLength conf := by simp [shiftLength] at *; omega
      have tagBound : smallShiftLength conf ≤ shiftLength conf - wordShiftAmount width := by
        simp [smallShiftLength, shiftLength] at *
        omega
      have positive : 0 < shiftLength conf - wordShiftAmount width := by
        simp [shiftLength] at *
        omega
      simp only [getRealAddr, stored, fast, ↓reduceIte, short, getAddr, BitVec.ushiftRight_or_distrib,
        getLowerBits_shiftBeyond conf v _ tagBound positive,
        bounded_shift_partial index (shiftLength conf) (wordShiftAmount width) ks bounded,
        shiftWordBytes good]
      simp
    · simpa [getRealAddr, getRealSimpleAddr, stored, fast, short] using
        getRealSimpleAddr_getAddr conf store heap index element curr v heapBound found stored good

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteArray
public import Flapjack.Byte.GetSetByte

@[expose] public section

/-! Byte extraction and injectivity of the source word-packing operation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.HolByte
open Classical
noncomputable section

/-- Reads at distinct byte positions ignore the write (Flapjack helper). -/
private theorem getByte_distinct {width : Nat} [NeZero width] (a b : BitVec width)
    (byte : BitVec 8) (word : BitVec width) (be : Bool)
    (h8 : 8 ≤ width) (different : byteIndex a be ≠ byteIndex b be) :
    getByte a (setByte b byte word be) be = getByte a word be := by
  have ha := byteIndex_add_le h8 a be
  have divA : 8 ∣ byteIndex a be := by unfold byteIndex; split <;> exact ⟨_, rfl⟩
  have divB : 8 ∣ byteIndex b be := by unfold byteIndex; split <;> exact ⟨_, rfl⟩
  obtain ⟨na, ea⟩ := divA
  obtain ⟨nb, eb⟩ := divB
  have apart : byteIndex a be + 8 ≤ byteIndex b be ∨ byteIndex b be + 8 ≤ byteIndex a be := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [getByte, BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]
  rw [getLsbD_setByte b byte word be _ (by omega)]
  rcases apart with h | h
  · simp [show byteIndex a be + i < byteIndex b be by omega,
      show ¬ byteIndex b be ≤ byteIndex a be + i by omega,
      show ¬ byteIndex b be + 8 ≤ byteIndex a be + i by omega]
  · simp [show byteIndex b be + 8 ≤ byteIndex a be + i by omega,
      show byteIndex b be ≤ byteIndex a be + i by omega,
      show ¬ byteIndex a be + i < byteIndex b be by omega,
      show byte.getLsbD (byteIndex a be + i - byteIndex b be) = false from
        BitVec.getLsbD_of_ge byte _ (by omega)]

/-- Distinct in-range addresses select distinct byte slots (Flapjack helper). -/
theorem indexDistinct {width : Nat} [NeZero width] (j i : Nat) (be : Bool)
    (good : goodDimindex width) (jbound : j < width / 8) (ibound : i < width / 8) (hne : i ≠ j) :
    byteIndex (BitVec.ofNat width i) be ≠ byteIndex (BitVec.ofNat width j) be := by
  have ib : i < 2 ^ width := by rcases good with hw | hw <;> subst width <;> norm_num at ibound ⊢ <;> omega
  have jb : j < 2 ^ width := by rcases good with hw | hw <;> subst width <;> norm_num at jbound ⊢ <;> omega
  have positive : 0 < width / 8 := by rcases good with hw | hw <;> subst width <;> decide
  simp only [byteIndex, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ib, Nat.mod_eq_of_lt jb,
    Nat.mod_eq_of_lt ibound, Nat.mod_eq_of_lt jbound]
  split <;> omega

/-- Read a byte written by a bounded packing operation (Flapjack helper). -/
private theorem readBytesAux {width : Nat} [NeZero width] (count start : Nat)
    (bytes : List (BitVec 8)) (word : BitVec width) (be : Bool) (i : Nat)
    (good : goodDimindex width) (fit : start + count ≤ width / 8)
    (inCount : i < count) (inBytes : i < bytes.length) :
    getByte (BitVec.ofNat width (start + i))
      (bytesToWord count (BitVec.ofNat width start) bytes word be) be = bytes[i] := by
  induction count generalizing start bytes i with
  | zero => omega
  | succ count ih =>
    cases bytes with
    | nil => simp at inBytes
    | cons byte bytes =>
      cases i with
      | zero =>
        have h8 : 8 ≤ width := by rcases good with h | h <;> omega
        simpa [bytesToWord] using getByte_setByte (BitVec.ofNat width start) byte
          (bytesToWord count (BitVec.ofNat width start + 1) bytes word be) be h8
      | succ i =>
        have h8 : 8 ≤ width := by rcases good with h | h <;> omega
        have diff : byteIndex (BitVec.ofNat width (start + (i + 1))) be ≠
            byteIndex (BitVec.ofNat width start) be :=
          indexDistinct start (start + (i + 1)) be good (by omega) (by omega) (by omega)
        simp only [bytesToWord, List.getElem_cons_succ]
        rw [getByte_distinct _ _ _ _ _ h8 diff]
        have next := ih (start + 1) bytes i (by omega) (by omega) (by simpa using inBytes)
        simpa [BitVec.ofNat_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using next

/-- Reading a packed in-range byte recovers the corresponding input byte. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "get_byte_bytes_to_word"
  (words_as_type_indexed_bitvec)]
theorem getByte_bytesToWord {width : Nat} [NeZero width] (i k : Nat) (be : Bool) :
    ∀ (bytes : List (BitVec 8)) (word : BitVec width)
      (h : i < bytes.length ∧ i < 2 ^ k ∧ 2 ^ k = width / 8 ∧ goodDimindex width),
      getByte (BitVec.ofNat width i) (bytesToWord (2 ^ k) 0 bytes word be) be = bytes[i]'h.1 := by
  intro bytes word h
  simpa using readBytesAux (2 ^ k) 0 bytes word be i h.2.2.2 (by omega) h.2.1 h.1

/-- Packing preserves the number of destination words (Flapjack helper). -/
private theorem packedLength {width : Nat} [NeZero width] (bytes : List (BitVec 8))
    (words : List (BitVec width)) (be : Bool) :
    (DataToWord.writeBytes bytes words be).length = words.length := by
  induction words generalizing bytes with
  | nil => rfl
  | cons x xs ih => simp [DataToWord.writeBytes, ih]

/-- Byte packing preserves the destination word count. -/
theorem writeBytes_wordCount {width : Nat} [NeZero width] (bytes : List (BitVec 8))
    (words : List (BitVec width)) (be : Bool) :
    (DataToWord.writeBytes bytes words be).length = words.length :=
  packedLength bytes words be

/-- Identify one packed word with its input byte group (Flapjack helper). -/
private theorem packedAt {width : Nat} [NeZero width] (words : List (BitVec width)) (bytes : List (BitVec 8))
    (be : Bool) (i : Nat) (h : i < words.length) :
    (DataToWord.writeBytes bytes words be)[i]'(by simpa [packedLength] using h) =
      bytesToWord (width / 8) 0 (bytes.drop (i * (width / 8))) words[i] be := by
  induction words generalizing bytes i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero => simp [DataToWord.writeBytes]
    | succ i =>
      simp only [DataToWord.writeBytes, List.getElem_cons_succ]
      rw [ih (bytes.drop (width / 8)) i (by simpa using h)]
      simp [List.drop_drop, Nat.succ_mul, Nat.add_comm]

/-- Flapjack infrastructure for the original byte-array memory proof: an
in-range byte is recovered from its containing packed word. -/
theorem getByte_writeBytes {width : Nat} [NeZero width] (words : List (BitVec width)) (bytes : List (BitVec 8))
    (be : Bool) (i : Nat) (good : goodDimindex width)
    (capacity : bytes.length ≤ words.length * (width / 8)) (bound : i < bytes.length) :
    getByte (BitVec.ofNat width (i % (width / 8)))
      ((writeBytes bytes words be)[i / (width / 8)]'(by
        rw [writeBytes_wordCount]
        have pos : 0 < width / 8 := by rcases good with h | h <;> subst width <;> decide
        exact (Nat.div_lt_iff_lt_mul pos).2 (by omega))) be = bytes[i] := by
  let d := width / 8
  let j := i / d
  let r := i % d
  change bytes.length ≤ words.length * d at capacity
  have pos : 0 < d := by rcases good with h | h <;> subst width <;> decide
  have rem : r < d := Nat.mod_lt _ pos
  have group : j < words.length := (Nat.div_lt_iff_lt_mul pos).2 (by omega)
  have division : j * d + r = i := by simpa [j, r, Nat.mul_comm] using Nat.div_add_mod i d
  have inputBound : r < (bytes.drop (j * d)).length := by simp only [List.length_drop]; omega
  have k : ∃ k, 2 ^ k = d := by
    rcases good with h | h <;> subst width
    · exact ⟨2, by decide⟩
    · exact ⟨3, by decide⟩
  obtain ⟨k, power⟩ := k
  change getByte (BitVec.ofNat width r) ((writeBytes bytes words be)[j]'(by simpa [writeBytes_wordCount] using group)) be = bytes[i]
  rw [packedAt words bytes be j group]
  have extracted := getByte_bytesToWord r k be (bytes.drop (j * d)) words[j]
    ⟨inputBound, by omega, power, good⟩
  simpa only [power, List.getElem_drop, division] using extracted

/-- Sufficient destination capacity makes byte packing injective. -/
private theorem packInjAux {width : Nat} [NeZero width] (words : List (BitVec width))
    (first second : List (BitVec 8)) (be : Bool) (good : goodDimindex width)
    (lengths : first.length = second.length) (capacity : first.length ≤ words.length * (width / 8))
    (equal : writeBytes first words be = writeBytes second words be) : first = second := by
  apply List.ext_getElem lengths
  intro i hi hj
  have pos : 0 < width / 8 := by rcases good with h | h <;> subst width <;> decide
  have group : i / (width / 8) < words.length := (Nat.div_lt_iff_lt_mul pos).2 (by omega)
  have wordEq : (writeBytes first words be)[i / (width / 8)]'(by simpa [writeBytes_wordCount] using group) =
      (writeBytes second words be)[i / (width / 8)]'(by simpa [writeBytes_wordCount] using group) := by
    have eq := congrArg (fun xs : List (BitVec width) => xs[i / (width / 8)]?) equal
    simpa [writeBytes_wordCount, group] using eq
  have f := getByte_writeBytes words first be i good capacity hi
  have s := getByte_writeBytes words second be i good (by omega) hj
  rw [← f, ← s, wordEq]

/-- The source byte-packing operation is injective under its original length bounds. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "write_bytes_inj"
  (words_as_type_indexed_bitvec)]
theorem writeBytesInj {width : Nat} [NeZero width] (be : Bool) :
    goodDimindex width → ∀ (words : List (BitVec width)) (first second : List (BitVec 8)),
      first.length = second.length ∧ first.length ≤ words.length * (width / 8) ∧
      words.length ≤ first.length / (width / 8) + 1 →
      (DataToWord.writeBytes first words be = DataToWord.writeBytes second words be ↔ first = second) := by
  intro good words first second ⟨lengths, capacity, _⟩
  constructor
  · exact packInjAux words first second be good lengths capacity
  · intro h; rw [h]

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

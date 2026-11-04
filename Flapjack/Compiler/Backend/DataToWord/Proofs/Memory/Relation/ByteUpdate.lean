import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BytePacking
import Flapjack.HolRef

/-! Byte updates in packed word payloads. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.HolByte

/-- A byte write changes precisely its eight bit positions. -/
theorem setByte_bit {width : Nat} [NeZero width] (address : BitVec width)
    (byte : BitVec 8) (word : BitVec width) (be : Bool) (j : Nat) (hj : j < width) :
    (setByte address byte word be).getLsbD j =
      if byteIndex address be ≤ j ∧ j < byteIndex address be + 8 then
        byte.getLsbD (j - byteIndex address be) else word.getLsbD j := by
  rw [getLsbD_setByte address byte word be j hj]
  by_cases low : j < byteIndex address be
  · simp [low, show ¬ byteIndex address be ≤ j by omega,
      show ¬ byteIndex address be + 8 ≤ j by omega]
  · by_cases high : byteIndex address be + 8 ≤ j
    · have zero : byte.getLsbD (j - byteIndex address be) = false :=
        BitVec.getLsbD_of_ge byte _ (by omega)
      simp [low, high, zero]
    · simp [low, high, show byteIndex address be ≤ j by omega,
        show j < byteIndex address be + 8 by omega]

/-- Two writes to the same byte lane leave only the later byte. -/
theorem setByte_overwrite {width : Nat} [NeZero width] (address : BitVec width)
    (first second : BitVec 8) (word : BitVec width) (be : Bool) :
    setByte address second (setByte address first word be) be = setByte address second word be := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [setByte_bit _ _ _ _ _ hj]
  split <;> rfl

/-- Writes to distinct byte lanes commute. -/
theorem setByte_commute {width : Nat} [NeZero width] (a b : BitVec width)
    (first second : BitVec 8) (word : BitVec width) (be : Bool)
    (different : byteIndex a be ≠ byteIndex b be) :
    setByte a first (setByte b second word be) be = setByte b second (setByte a first word be) be := by
  have divA : 8 ∣ byteIndex a be := by unfold byteIndex; split <;> exact ⟨_, rfl⟩
  have divB : 8 ∣ byteIndex b be := by unfold byteIndex; split <;> exact ⟨_, rfl⟩
  obtain ⟨na, ea⟩ := divA
  obtain ⟨nb, eb⟩ := divB
  have apart : byteIndex a be + 8 ≤ byteIndex b be ∨ byteIndex b be + 8 ≤ byteIndex a be := by omega
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [setByte_bit _ _ _ _ _ hj]
  by_cases ina : byteIndex a be ≤ j ∧ j < byteIndex a be + 8
  · have notB : ¬ (byteIndex b be ≤ j ∧ j < byteIndex b be + 8) := by omega
    simp [ina, notB]
  · by_cases inb : byteIndex b be ≤ j ∧ j < byteIndex b be + 8 <;> simp [ina, inb]

/-- In-range byte positions select different lanes. -/
private theorem indexDistinct {width : Nat} [NeZero width] (j i : Nat) (be : Bool)
    (good : goodDimindex width) (jbound : j < width / 8) (ibound : i < width / 8) (hne : i ≠ j) :
    byteIndex (BitVec.ofNat width i) be ≠ byteIndex (BitVec.ofNat width j) be := by
  have ib : i < 2 ^ width := by rcases good with hw | hw <;> subst width <;> norm_num at ibound ⊢ <;> omega
  have jb : j < 2 ^ width := by rcases good with hw | hw <;> subst width <;> norm_num at jbound ⊢ <;> omega
  simp only [byteIndex, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ib, Nat.mod_eq_of_lt jb,
    Nat.mod_eq_of_lt ibound, Nat.mod_eq_of_lt jbound]
  split <;> omega

/-- Updating one byte of a bounded packed group agrees with writing that byte
into its corresponding lane of the packed word. -/
theorem bytesToWord_setByte_aux {width : Nat} [NeZero width] (count start : Nat)
    (bytes : List (BitVec 8)) (word : BitVec width) (be : Bool) (i : Nat) (byte : BitVec 8)
    (good : goodDimindex width) (fit : start + count ≤ width / 8)
    (inCount : i < count) (inBytes : i < bytes.length) :
    setByte (BitVec.ofNat width (start + i)) byte
      (bytesToWord count (BitVec.ofNat width start) bytes word be) be =
    bytesToWord count (BitVec.ofNat width start) (bytes.set i byte) word be := by
  induction count generalizing start bytes i with
  | zero => omega
  | succ count ih =>
    cases bytes with
    | nil => simp at inBytes
    | cons head tail =>
      cases i with
      | zero =>
        simp only [Nat.add_zero, bytesToWord, List.set_cons_zero]
        exact setByte_overwrite _ _ _ _ _
      | succ i =>
        have distinct : byteIndex (BitVec.ofNat width (start + (i + 1))) be ≠
            byteIndex (BitVec.ofNat width start) be :=
          indexDistinct start (start + (i + 1)) be good (by omega) (by omega) (by omega)
        simp only [bytesToWord, List.set_cons_succ]
        rw [setByte_commute _ _ _ _ _ _ distinct]
        have next := ih (start + 1) tail i (by omega) (by omega) (by simpa using inBytes)
        simpa [BitVec.ofNat_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          congrArg (fun w => setByte (BitVec.ofNat width start) head w be) next

/-- Updating an in-range input byte is exactly a write to its packed lane. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "set_byte_bytes_to_word"
  (words_as_type_indexed_bitvec)]
theorem setByte_bytesToWord {width : Nat} [NeZero width] (i k : Nat) (bytes : List (BitVec 8))
    (byte : BitVec 8) (word : BitVec width) (be : Bool) :
    i < bytes.length ∧ i < 2 ^ k ∧ 2 ^ k = width / 8 ∧ goodDimindex width →
    setByte (BitVec.ofNat width i) byte (bytesToWord (2 ^ k) 0 bytes word be) be =
      bytesToWord (2 ^ k) 0 (bytes.set i byte) word be := by
  rintro ⟨inBytes, inCount, power, good⟩
  simpa using bytesToWord_setByte_aux (2 ^ k) 0 bytes word be i byte good (by omega) inCount inBytes

/-- Packing a fixed number of bytes ignores updates beyond that prefix. -/
theorem bytesToWord_set_outside {width : Nat} [NeZero width] (count : Nat)
    (address : BitVec width) (bytes : List (BitVec 8)) (word : BitVec width) (be : Bool)
    (i : Nat) (byte : BitVec 8) (outside : count ≤ i) :
    bytesToWord count address (bytes.set i byte) word be = bytesToWord count address bytes word be := by
  induction count generalizing address bytes i with
  | zero => rfl
  | succ count ih =>
    cases bytes with
    | nil => simp [bytesToWord]
    | cons head tail =>
      cases i with
      | zero => omega
      | succ i =>
        simp only [List.set_cons_succ, bytesToWord]
        rw [ih _ _ _ (by omega)]

/-- An in-range source-byte update changes exactly one packed destination word. -/
theorem writeBytes_setByte64 (bytes : List (BitVec 8)) (words : List (BitVec 64))
    (be : Bool) (i : Nat) (byte : BitVec 8) (inBytes : i < bytes.length)
    (capacity : bytes.length ≤ words.length * 8) :
    DataToWord.writeBytes (bytes.set i byte) words be =
      (DataToWord.writeBytes bytes words be).modify (i / 8)
        (fun word => setByte (BitVec.ofNat 64 (i % 8)) byte word be) := by
  induction words generalizing bytes i with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, Nat.le_zero] at capacity
    omega
  | cons word words ih =>
    by_cases first : i < 8
    · have div : i / 8 = 0 := Nat.div_eq_of_lt first
      have mod : i % 8 = i := Nat.mod_eq_of_lt first
      have lane := setByte_bytesToWord i 3 bytes byte word be ⟨inBytes, by simpa using first, by decide, Or.inr rfl⟩
      norm_num at lane
      simp only [DataToWord.writeBytes, Nat.reduceDiv, div, mod, List.modify_zero_cons]
      rw [← lane, List.drop_set_of_lt first]
    · have later : 8 ≤ i := by omega
      have div : i / 8 = (i - 8) / 8 + 1 := by omega
      have mod : i % 8 = (i - 8) % 8 := by omega
      have inside : i - 8 < (bytes.drop 8).length := by simp; omega
      have cap : (bytes.drop 8).length ≤ words.length * 8 := by simp at capacity ⊢; omega
      have firstWord := bytesToWord_set_outside 8 (0 : BitVec 64) bytes word be i byte later
      simp only [DataToWord.writeBytes, Nat.reduceDiv, div, mod, List.modify_succ_cons]
      rw [firstWord, List.drop_set, if_neg first]
      exact congrArg (List.cons _) (ih _ _ inside cap)

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

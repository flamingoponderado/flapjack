module
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate
public import Flapjack.SemanticPrimitivesHOL.Thunk
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord Flapjack.HolByte

@[expose] public section
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
/-- Read a word and report whether the address is valid and contains a word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "read_word_def"
  (words_as_type_indexed_bitvec)]
noncomputable def readWord {width : Nat} [NeZero width] {α : Type}
    (dm : α → Bool) (m : α → WordLocW width) (a : α) : BitVec width × Bool :=
  (wordSemTheWord (m a), dm a && wordSemIsWordLoc (m a))

open Classical in
/-- XOR words in memory in the original one- or two-word recursive steps. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_xor_bytes_def"
  (words_as_type_indexed_bitvec)]
noncomputable def wordXorBytes {width : Nat} [NeZero width]
    (a1 a2 len : BitVec width) (dm : BitVec width → Bool) (m : BitVec width → WordLocW width) :
    Option (BitVec width → WordLocW width) :=
  if len.toNat < (2 : BitVec width).toNat ∨ ¬ goodDimindex width then
    if len = 0 then some m else
      let (w1, c1) := readWord dm m a1
      let (w2, c2) := readWord dm m a2
      let next := fun k => if k = a2 then WordLocW.word (w1 ^^^ w2) else m k
      if c1 && c2 then some next else none
  else
    let (w1, c1) := readWord dm m a1
    let (w2, c2) := readWord dm m a2
    let (w3, c3) := readWord dm m (a1 + wordSemBytesInWord)
    let (w4, c4) := readWord dm m (a2 + wordSemBytesInWord)
    let next := fun k => if k = a2 + wordSemBytesInWord then WordLocW.word (w3 ^^^ w4)
      else if k = a2 then WordLocW.word (w1 ^^^ w2) else m k
    if c1 && c2 && c3 && c4 then
      wordXorBytes (a1 + 2 * wordSemBytesInWord) (a2 + 2 * wordSemBytesInWord) (len - 2) dm next
    else none
termination_by len.toNat
decreasing_by
  simp only [not_or, not_not] at *
  rename_i h
  rcases h.2 with hw | hw <;> subst width <;> simp_all [BitVec.toNat_sub, BitVec.toNat_ofNat] <;> omega

/-- Allocate the zero-word buffer used by byte packing. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "make_zeros_def"
  (words_as_type_indexed_bitvec)]
def makeZeros {width : Nat} [NeZero width] (vals : List (BitVec 8)) : List (BitVec width) :=
  List.replicate (vals.length / (width / 8) + 1) 0

/-- XOR a word prefix, returning any unused suffix of the second list. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "xor_words_def"
  (words_as_type_indexed_bitvec)]
def xorWords {width : Nat} [NeZero width] : List (BitVec width) → List (BitVec width) → Option (List (BitVec width))
  | [], ys => some ys
  | _ :: _, [] => none
  | x :: xs, y :: ys => (xorWords xs ys).map (fun rest => (x ^^^ y) :: rest)


/-- XOR commutes with inserting corresponding bytes into the same lane. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_xor_set_byte"
  (words_as_type_indexed_bitvec)]
theorem wordXorSetByte {width : Nat} [NeZero width] (a : BitVec width) (h1 h2 : BitVec 8)
    (w1 w2 : BitVec width) (be : Bool) :
    setByte a h1 w1 be ^^^ setByte a h2 w2 be = setByte a (h1 ^^^ h2) (w1 ^^^ w2) be := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor, setByte_bit _ _ _ _ _ hi]
  split <;> simp

/-- Successful byte XOR has the original length bounds. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "xor_bytes_length"]
theorem xorBytesLength (xs ys zs : List (BitVec 8)) (h : Flapjack.SemanticPrimitivesHOL.xorBytes xs ys = some zs) :
    xs.length ≤ zs.length ∧ zs.length = ys.length := by
  induction xs generalizing ys zs with
  | nil => simp [Flapjack.SemanticPrimitivesHOL.xorBytes] at h; subst zs; simp
  | cons x xs ih =>
    cases ys with
    | nil => simp [Flapjack.SemanticPrimitivesHOL.xorBytes] at h
    | cons y ys =>
      simp only [Flapjack.SemanticPrimitivesHOL.xorBytes] at h
      cases recEq : Flapjack.SemanticPrimitivesHOL.xorBytes xs ys with
      | none => simp [recEq] at h
      | some rest =>
        simp [recEq] at h
        subst zs
        have result := ih ys rest recEq
        simp only [List.length_cons] at *
        omega


/-- Packing two byte lists commutes with their successful bytewise XOR. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "xor_bytes_bytes_to_word"
  (words_as_type_indexed_bitvec)]
theorem xorBytesBytesToWord {width : Nat} [NeZero width] (k : Nat) (xs ys zs : List (BitVec 8)) (a : BitVec width) (be : Bool)
    (h : SemanticPrimitivesHOL.xorBytes xs ys = some zs) :
    bytesToWord k a xs 0 be ^^^ bytesToWord k a ys 0 be = bytesToWord k a zs 0 be := by
  induction k generalizing xs ys zs a with
  | zero => simp [bytesToWord]
  | succ k ih =>
    cases xs with
    | nil => simp [SemanticPrimitivesHOL.xorBytes] at h; subst zs; simp [bytesToWord]
    | cons x xs =>
      cases ys with
      | nil => simp [SemanticPrimitivesHOL.xorBytes] at h
      | cons y ys =>
        simp only [SemanticPrimitivesHOL.xorBytes] at h
        cases recEq : SemanticPrimitivesHOL.xorBytes xs ys with
        | none => simp [recEq] at h
        | some rest =>
          simp [recEq] at h
          subst zs
          simp only [bytesToWord]
          rw [wordXorSetByte, ih xs ys rest (a+1) recEq]

/-- Dropping the same prefix preserves a successful byte XOR. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "xor_bytes_drop"]
theorem xorBytesDrop (n : Nat) (xs ys zs : List (BitVec 8)) (h : SemanticPrimitivesHOL.xorBytes xs ys = some zs) :
    SemanticPrimitivesHOL.xorBytes (xs.drop n) (ys.drop n) = some (zs.drop n) := by
  induction xs generalizing ys zs n with
  | nil => simp [SemanticPrimitivesHOL.xorBytes] at h; subst zs; simp [SemanticPrimitivesHOL.xorBytes]
  | cons x xs ih =>
    cases ys with
    | nil => simp [SemanticPrimitivesHOL.xorBytes] at h
    | cons y ys =>
      cases n with
      | zero => simpa using h
      | succ n =>
        simp only [SemanticPrimitivesHOL.xorBytes] at h
        cases recEq : SemanticPrimitivesHOL.xorBytes xs ys with
        | none => simp [recEq] at h
        | some rest =>
          simp [recEq] at h
          subst zs
          simpa using ih n ys rest recEq


/-- Successful byte XOR agrees with packed XOR for zero-initialized word lists. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "xor_bytes_xor_words" 18451
  (words_as_type_indexed_bitvec)]
theorem xorBytesXorWordsAux {width : Nat} [NeZero width] (zs1 zs2 : List (BitVec width))
    (vals1 vals2 res : List (BitVec 8)) (be : Bool)
    (h : SemanticPrimitivesHOL.xorBytes vals1 vals2 = some res)
    (good : goodDimindex width) (z1 : zs1.Forall (fun w => w = 0)) (z2 : zs2.Forall (fun w => w = 0))
    (len1 : zs1.length = vals1.length / (width / 8) + 1)
    (len2 : zs2.length = vals2.length / (width / 8) + 1) :
    xorWords (writeBytes vals1 zs1 be) (writeBytes vals2 zs2 be) = some (writeBytes res zs2 be) := by
  induction zs1 generalizing zs2 vals1 vals2 res with
  | nil => simp at len1
  | cons w ws ih =>
    cases zs2 with
    | nil => simp at len2
    | cons v vs =>
      simp only [List.forall_cons] at z1 z2
      have wz : w = 0 := z1.1
      have vz : v = 0 := z2.1
      subst w; subst v
      have z1t : ws.Forall (fun w => w = 0) := z1.2
      have z2t : vs.Forall (fun w => w = 0) := z2.2
      have packed := xorBytesBytesToWord (width := width) (width / 8) vals1 vals2 res 0 be h
      have dropped := xorBytesDrop (width / 8) vals1 vals2 res h
      simp only [writeBytes, xorWords, Option.map_eq_some_iff, List.cons.injEq]
      refine ⟨writeBytes (res.drop (width / 8)) vs be, ?_, packed, rfl⟩
      by_cases short : vals1.length < width / 8
      · have div0 : vals1.length / (width / 8) = 0 := Nat.div_eq_of_lt short
        have wsNil : ws = [] := by cases ws with | nil => rfl | cons q qs => simp [div0] at len1
        have dropNil : vals1.drop (width / 8) = [] := List.drop_eq_nil_of_le (by omega)
        simp [dropNil, SemanticPrimitivesHOL.xorBytes] at dropped
        subst ws
        simp [writeBytes, xorWords, dropped]
      · have long1 : width / 8 ≤ vals1.length := by omega
        have lengths := xorBytesLength vals1 vals2 res h
        have long2 : width / 8 ≤ vals2.length := by omega
        have l1 : ws.length = (vals1.drop (width / 8)).length / (width / 8) + 1 := by
          simp only [List.length_drop, List.length_cons] at len1 ⊢
          rcases good with hw | hw <;> subst width <;> norm_num at * <;> omega
        have l2 : vs.length = (vals2.drop (width / 8)).length / (width / 8) + 1 := by
          simp only [List.length_drop, List.length_cons] at len2 ⊢
          rcases good with hw | hw <;> subst width <;> norm_num at * <;> omega
        exact ih vs _ _ _ dropped z1t z2t l1 l2


/-- Packing successful byte XOR agrees with XORing the packed zero buffers. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "xor_bytes_xor_words" 18483
  (words_as_type_indexed_bitvec)]
theorem xorBytesXorWords {width : Nat} [NeZero width] (vals1 vals2 res : List (BitVec 8)) (be : Bool)
    (h : SemanticPrimitivesHOL.xorBytes vals1 vals2 = some res) (good : goodDimindex width) :
    xorWords (writeBytes vals1 (makeZeros (width := width) vals1) be)
      (writeBytes vals2 (makeZeros (width := width) vals2) be) =
      some (writeBytes res (makeZeros (width := width) vals2) be : List (BitVec width)) := by
  apply xorBytesXorWordsAux (makeZeros vals1) (makeZeros vals2) vals1 vals2 res be h good
  · simp [makeZeros, List.forall_iff_forall_mem]
  · simp [makeZeros, List.forall_iff_forall_mem]
  · simp [makeZeros]
  · simp [makeZeros]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

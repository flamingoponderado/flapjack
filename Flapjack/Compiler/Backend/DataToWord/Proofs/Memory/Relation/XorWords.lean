module
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate
public import Flapjack.SemanticPrimitivesHOL.Thunk
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
open Flapjack Flapjack.Compiler.Backend Flapjack.HolByte

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

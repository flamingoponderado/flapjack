module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockTests

@[expose] public section
/-! Recovering constructor tags and lengths from encoded headers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack
/-- A header exposes each in-range tag bit. This is Flapjack bit-vector infrastructure. -/
theorem headerTagBit {width : Nat} [NeZero width] (conf : Config) (tag len i : Nat)
    (hwidth : 4 ≤ width) (hconfig : conf.lenSize + 2 < width)
    (hi : i < width - conf.lenSize - 2) :
    (makeHeader conf (BitVec.ofNat width tag) len).getLsbD (i + 2) = tag.testBit i := by
  have pos : i + 2 < width := by omega
  have high : i + 2 < width - conf.lenSize := by omega
  have modtwo : 2 % 2 ^ width = 2 := by
    apply Nat.mod_eq_of_lt
    have : 2 ^ 2 ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have three : (3 : Nat).testBit (i + 2) = false := Nat.testBit_lt_two_pow (by
    have pow := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ i + 2 by omega)
    omega)
  have ib : i < width := by omega
  have high' : ¬ width ≤ i + 2 + conf.lenSize := by omega
  simp [makeHeader, BitVec.getElem_eq_testBit_toNat, pos, modtwo, three, ib, high']
/-- A header exposes each in-range length bit. This is Flapjack bit-vector infrastructure. -/
theorem headerLengthBit {width : Nat} [NeZero width] (conf : Config) (tag len i : Nat)
    (hwidth : 4 ≤ width) (hconfig : conf.lenSize + 2 < width)
    (hTag : tag < 2 ^ (width - conf.lenSize - 2)) (hi : i < conf.lenSize) :
    (makeHeader conf (BitVec.ofNat width tag) len).getLsbD (i + (width - conf.lenSize)) = len.testBit i := by
  have pos : i + (width - conf.lenSize) < width := by omega
  have high : width - conf.lenSize ≤ i + (width - conf.lenSize) := by omega
  have modtwo : 2 % 2 ^ width = 2 := by
    apply Nat.mod_eq_of_lt
    have : 2 ^ 2 ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have three : (3 : Nat).testBit (i + (width - conf.lenSize)) = false := Nat.testBit_lt_two_pow (by
    have pow := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ i + (width - conf.lenSize) by omega)
    omega)
  have tagZero : tag.testBit (i + (width - conf.lenSize) - 2) = false := Nat.testBit_lt_two_pow (by
    have pow := Nat.pow_le_pow_right (n := 2) (by decide)
      (show width - conf.lenSize - 2 ≤ i + (width - conf.lenSize) - 2 by omega)
    omega)
  have ib : i < width := by omega
  simp [makeHeader, BitVec.getElem_eq_testBit_toNat, pos, modtwo, three, tagZero, ib, high]

/-- Successfully encoded headers are equal exactly when their tags and lengths agree. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "encode_header_EQ"
  (words_as_type_indexed_bitvec)]
theorem encodeHeader_eq {width : Nat} [NeZero width] (conf : Config) (t1 l1 t2 l2 : Nat) (w1 w2 : BitVec width) :
    encodeHeader conf t1 l1 = some w1 ∧ encodeHeader conf t2 l2 = some w2 ∧
      conf.lenSize + 2 < width → (w1 = w2 ↔ t1 = t2 ∧ l1 = l2) := by
  rintro ⟨h1, h2, config⟩
  have c1 : t1 < 2 ^ (width - conf.lenSize - 2) ∧ t1 < 2 ^ width / 16 ∧
      l1 < 2 ^ (width - 4) ∧ l1 < 2 ^ conf.lenSize := by
    by_contra no
    simp [encodeHeader, no] at h1
  have c2 : t2 < 2 ^ (width - conf.lenSize - 2) ∧ t2 < 2 ^ width / 16 ∧
      l2 < 2 ^ (width - 4) ∧ l2 < 2 ^ conf.lenSize := by
    by_contra no
    simp [encodeHeader, no] at h2
  have width4 : 4 ≤ width := by
    by_contra bad
    have cases : width = 0 ∨ width = 1 ∨ width = 2 ∨ width = 3 := by omega
    rcases cases with h | h | h | h <;> subst width <;> norm_num at c1
  have e1 : makeHeader conf (BitVec.ofNat width t1) l1 = w1 := by
    simpa [encodeHeader, c1] using h1
  have e2 : makeHeader conf (BitVec.ofNat width t2) l2 = w2 := by
    simpa [encodeHeader, c2] using h2
  constructor
  · intro equal
    have same : makeHeader conf (BitVec.ofNat width t1) l1 = makeHeader conf (BitVec.ofNat width t2) l2 :=
      e1.trans (equal.trans e2.symm)
    constructor
    · apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < width - conf.lenSize - 2
      · have bits := congrArg (fun w : BitVec width => w.getLsbD (i + 2)) same
        rw [headerTagBit conf t1 l1 i width4 config hi, headerTagBit conf t2 l2 i width4 config hi] at bits
        exact bits
      · have pow : 2 ^ (width - conf.lenSize - 2) ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        have z1 : t1.testBit i = false := Nat.testBit_lt_two_pow (by omega)
        have z2 : t2.testBit i = false := Nat.testBit_lt_two_pow (by omega)
        rw [z1, z2]
    · apply Nat.eq_of_testBit_eq
      intro i
      by_cases hi : i < conf.lenSize
      · have bits := congrArg (fun w : BitVec width => w.getLsbD (i + (width - conf.lenSize))) same
        rw [headerLengthBit conf t1 l1 i width4 config c1.1 hi,
          headerLengthBit conf t2 l2 i width4 config c2.1 hi] at bits
        exact bits
      · have pow : 2 ^ conf.lenSize ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega)
        have z1 : l1.testBit i = false := Nat.testBit_lt_two_pow (by omega)
        have z2 : l2.testBit i = false := Nat.testBit_lt_two_pow (by omega)
        rw [z1, z2]
  · rintro ⟨rfl, rfl⟩
    exact e1.symm.trans e2

/-- A successfully encoded constructor header exposes its tag under the source
mask, and the tag fits in a machine word with four low bits reserved. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "encode_header_tag_mask"
  (words_as_type_indexed_bitvec)]
theorem encodeHeader_tagMask {width : Nat} [NeZero width] (conf : Config) (tag len : Nat) (w : BitVec width)
    (encoded : encodeHeader conf (4 * tag) len = some w) (good : goodDimindex width) :
    tag < 2 ^ width / 16 ∧
    (w &&& (holWordSlice (width - conf.lenSize - 1) 2 (~~~(0 : BitVec width)) ||| 2)) =
      BitVec.ofNat width (16 * tag + 2) := by
  have bounds : 4 * tag < 2 ^ (width - conf.lenSize - 2) ∧ 4 * tag < 2 ^ width / 16 ∧
      len < 2 ^ (width - 4) ∧ len < 2 ^ conf.lenSize := by
    by_contra no
    simp [encodeHeader, no] at encoded
  have weq : makeHeader conf (BitVec.ofNat width (4 * tag)) len = w := by
    simpa [encodeHeader, bounds] using encoded
  constructor
  · omega
  · rw [← weq]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hwidth : 4 ≤ width := by rcases good with h | h <;> omega
    have modtwo : 2 % 2 ^ width = 2 := Nat.mod_eq_of_lt (by
      have p := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ width by omega)
      omega)
    have bitResult (j : Nat) (hj : 2 ≤ j) :
        (16 * tag + 2).testBit j = (4 * tag).testBit (j - 2) := by
      have div : (16 * tag + 2) / 4 = 4 * tag := by omega
      conv_lhs => rw [show j = (j - 2) + 2 by omega, Nat.testBit_add]
      simpa using congrArg (fun n : Nat => n.testBit (j - 2)) div
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, holWordSlice, getLsbD_holFcpWord,
      hi, decide_true, Bool.true_and, BitVec.getLsbD_not]
    simp [makeHeader, BitVec.getElem_eq_testBit_toNat, hi, modtwo]
    by_cases low : i < 2
    · have cases : i = 0 ∨ i = 1 := by omega
      rcases cases with rfl | rfl <;> simp [Nat.testBit, Nat.shiftRight_eq_div_pow] <;> omega
    · have two : 2 ≤ i := by omega
      rw [bitResult i two]
      have three : (3 : Nat).testBit i = false := Nat.testBit_lt_two_pow (by
        have p := Nat.pow_le_pow_right (n := 2) (by decide) two
        omega)
      have b2 : (2 : Nat).testBit i = false := Nat.testBit_lt_two_pow (by
        have p := Nat.pow_le_pow_right (n := 2) (by decide) two
        omega)
      have ib : i - 2 < width := by omega
      by_cases high : width ≤ i + conf.lenSize
      · have hp : width - conf.lenSize - 2 ≤ i - 2 := by omega
        have pow := Nat.pow_le_pow_right (n := 2) (by decide) hp
        have z : (4 * tag).testBit (i - 2) = false := Nat.testBit_lt_two_pow (by omega)
        simp [two, three, b2, ib, high, z, show ¬ i ≤ width - conf.lenSize - 1 by omega]
      · simp [two, three, b2, ib, high, show i ≤ width - conf.lenSize - 1 by omega,
          show i ≤ width - 1 by omega]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockTests
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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

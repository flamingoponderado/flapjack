module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare
@[expose] public section

/-! Numeric bounds checks over the full memory relation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
/-- A related numeric value supports the original strict and non-strict
unsigned bounds checks after rotating its representation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_bounds_check"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_boundsCheck {width : Nat} [NeZero width] (conf : Config) (be : Bool)
    (ts : Nat) (refs : Spt (BvlSem.Ref DataSem.Value)) (sp : Nat)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i : Int) (w : BitVec width) (vars : List (DataSem.Value × WordLocW width)) (n : Nat)
    (rel : memoryRel conf be ts refs sp store memory domain ((.number i, .word w) :: vars))
    (small : smallInt width (Int.ofNat n)) (good : goodDimindex width) :
    (w.rotateRight 2 < BitVec.ofNat width n ↔ 0 ≤ i ∧ i < Int.ofNat n) ∧
    (w.rotateRight 2 ≤ BitVec.ofNat width n ↔ 0 ≤ i ∧ i ≤ Int.ofNat n) := by
  obtain ⟨v, eq, bit⟩ := memoryRel_anyNumberImp conf be ts refs sp store memory domain i (.word w) vars ⟨good, rel⟩
  have veq : v = w := WordLocW.word.inj eq.symm
  subst v
  by_cases smallI : smallInt width i
  · have eq := memoryRel_numberImp conf be ts refs sp store memory domain i (.word w) vars ⟨good, smallI, rel⟩
    have weq : w = smallnum i := WordLocW.word.inj eq
    subst w
    by_cases neg : i < 0
    · have bounds := smallnum_signedBounds good i smallI
      have sign : (smallnum i : BitVec width).msb = true := by
        rw [← BitVec.slt_zero_eq_msb, BitVec.slt_eq_decide, decide_eq_true_eq]
        have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
        rw [smallnum_i2w, BitVec.toInt_ofInt_eq_self pos bounds.1 bounds.2]
        simp
        omega
      have high : ((smallnum i : BitVec width).rotateRight 2).getLsbD (width - 3) = true := by
        rw [BitVec.msb_eq_getLsbD_last] at sign
        rcases good with hw | hw <;> subst width <;> simpa [BitVec.getLsbD_rotateRight] using sign
      change ((smallnum i : BitVec width).rotateRight 2).toNat.testBit (width - 3) = true at high
      have highBound := Nat.ge_two_pow_of_testBit high
      rcases good with hw | hw <;> subst width
      all_goals
        simp only [BitVec.lt_def, BitVec.le_def, BitVec.toNat_ofNat]
        norm_num [smallInt] at small highBound ⊢
        omega
    · cases i with
      | negSucc k => simp at neg
      | ofNat k =>
        have smEq : (smallnum (Int.ofNat k) : BitVec width) = BitVec.ofNat width (4 * k) := by
          simp [smallnum, Int.not_lt.mpr (Int.natCast_nonneg k)]
          congr 1
        have fourBound : 4 * k < 2 ^ width := by
          rcases good with hw | hw <;> subst width <;> norm_num [smallInt] at smallI ⊢ <;> omega
        have enc : (BitVec.ofNat width (4 * k)).toNat = 4 * k := by
          simp [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fourBound]
        have shiftZero : (4 * k * 2 ^ (width - 2)) % 2 ^ width = 0 := by
          rcases good with hw | hw <;> subst width <;> norm_num <;> omega
        have rotateNat : ((smallnum (Int.ofNat k) : BitVec width).rotateRight 2).toNat = k := by
          rw [smEq, BitVec.toNat_rotateRight, enc]
          rcases good with hw | hw <;> subst width
          all_goals
            norm_num [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq] at shiftZero ⊢
            simp [shiftZero]
        rcases good with hw | hw <;> subst width
        all_goals
          simp only [BitVec.lt_def, BitVec.le_def, BitVec.toNat_ofNat, rotateNat]
          norm_num [smallInt] at small smallI ⊢
          omega
  · have hbit : w.getLsbD 0 = true := bit.mpr smallI
    have high : (w.rotateRight 2).getLsbD (width - 2) = true := by
      rcases good with hw | hw <;> subst width <;> simp [hbit]
    change (w.rotateRight 2).toNat.testBit (width - 2) = true at high
    have highBound := Nat.ge_two_pow_of_testBit high
    rcases good with hw | hw <;> subst width
    all_goals
      simp only [BitVec.lt_def, BitVec.le_def, BitVec.toNat_ofNat]
      norm_num [smallInt] at small smallI highBound ⊢
      omega
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

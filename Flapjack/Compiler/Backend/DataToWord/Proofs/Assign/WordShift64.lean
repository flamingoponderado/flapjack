module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WriteWord64
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.ShiftVar
@[expose] public section

/-! The 32-bit lowering of a 64-bit shift, following the HOL assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

namespace Shift64Witness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end Shift64Witness

private theorem lslHighSmall (v : BitVec 64) (n : Nat) (hn : n < 32) :
    (v.setWidth 32 >>> (32 - n)) ||| ((v >>> (32 : Nat)).setWidth 32 <<< n) =
      ((v <<< n) >>> (32 : Nat)).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth, hi]
  by_cases h : i < n
  · have h1 : 32 - n + i < 32 := by omega
    have h2 : 32 + i < 64 := by omega
    have h3 : ¬ 32 + i < n := by omega
    have h4 : 32 - n + i = 32 + i - n := by omega
    simp [h, h2, h3, h4, show 32 + i - n < 32 by omega]
  · have h1 : ¬ 32 - n + i < 32 := by omega
    have h2 : 32 + i < 64 := by omega
    have h3 : ¬ 32 + i < n := by omega
    have h4 : 32 + (i - n) = 32 + i - n := by omega
    simp [h, h1, h2, h3, h4]

private theorem lslHighBig (v : BitVec 64) (n : Nat) (hn : 32 ≤ n) :
    v.setWidth 32 <<< (n - 32) = ((v <<< n) >>> (32 : Nat)).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    hi]
  have h1 : (i < n - 32) ↔ (32 + i < n) := by omega
  have h2 : 32 + i < 64 := by omega
  have h3 : i - (n - 32) = 32 + i - n := by omega
  simp [h1, h2, h3]

private theorem lsrLowSmall (v : BitVec 64) (n : Nat) (hn : n < 32) :
    ((v >>> (32 : Nat)).setWidth 32 <<< (32 - n)) ||| (v.setWidth 32 >>> n) =
      (v >>> n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight,     BitVec.getLsbD_setWidth, hi]
  by_cases h : n + i < 32
  · have h1 : i < 32 - n := by omega
    simp [h, h1]
  · have h1 : ¬ i < 32 - n := by omega
    have h2 : 32 + (i - (32 - n)) = n + i := by omega
    simp [h, h1, h2]

private theorem lsrHigh (v : BitVec 64) (n : Nat) :
    (v >>> (32 : Nat)).setWidth 32 >>> n = ((v >>> n) >>> (32 : Nat)).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi]
  by_cases h : n + i < 32
  · simp [h, show 32 + (n + i) = n + (32 + i) by omega]
  · simp [h, BitVec.getLsbD_of_ge v (n + (32 + i)) (by omega)]

private theorem asrHigh (v : BitVec 64) (n : Nat) :
    ((v >>> (32 : Nat)).setWidth 32).sshiftRight n =
      ((v.sshiftRight n) >>> (32 : Nat)).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmsb : ((v >>> (32 : Nat)).setWidth 32).msb = v.msb := by
    simp [BitVec.msb_eq_getLsbD_last]
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, hmsb]
  have h1 : ¬ 32 ≤ i := by omega
  have h2 : ¬ 64 ≤ 32 + i := by omega
  have h3 : (n + i < 32) ↔ (n + (32 + i) < 64) := by omega
  have h4 : 32 + (n + i) = n + (32 + i) := by omega
  simp [hi, h1, h2, h3, h4]
  split <;> simp_all

private theorem asrLowSmall (v : BitVec 64) (n : Nat) (hn : n < 32) :
    (v.sshiftRight n).setWidth 32 = (v >>> n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_ushiftRight]
  simp [hi, show ¬ 64 ≤ i by omega, show n + i < 64 by omega]

private theorem asrLowBig (v : BitVec 64) (n : Nat) (hn : 32 ≤ n) :
    ((v >>> (32 : Nat)).setWidth 32).sshiftRight (n - 32) =
      (v.sshiftRight n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmsb : ((v >>> (32 : Nat)).setWidth 32).msb = v.msb := by
    simp [BitVec.msb_eq_getLsbD_last]
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_sshiftRight,
    BitVec.getLsbD_ushiftRight, hmsb]
  have h1 : ¬ 32 ≤ i := by omega
  have h2 : ¬ 64 ≤ i := by omega
  have h3 : (n - 32 + i < 32) ↔ (n + i < 64) := by omega
  have h4 : 32 + (n - 32 + i) = n + i := by omega
  simp [hi, h1, h2, h3, h4]
  split <;> simp_all

private theorem rorLowSmall (v : BitVec 64) (n : Nat) (hn : n < 32) :
    ((v >>> (32 : Nat)).setWidth 32 <<< (32 - n)) ||| (v.setWidth 32 >>> n) =
      (v.rotateRight n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateRight, hi, Nat.mod_eq_of_lt (show n < 64 by omega),
    show i < 64 - n by omega]
  by_cases h : n + i < 32
  · have h1 : i < 32 - n := by omega
    simp [h, h1]
  · have h1 : ¬ i < 32 - n := by omega
    have h2 : 32 + (i - (32 - n)) = n + i := by omega
    simp [h, h1, h2]

private theorem rorHighSmall (v : BitVec 64) (n : Nat) (hn : n < 32) :
    (v.setWidth 32 <<< (32 - n)) ||| ((v >>> (32 : Nat)).setWidth 32 >>> n) =
      ((v.rotateRight n) >>> (32 : Nat)).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateRight, hi, Nat.mod_eq_of_lt (show n < 64 by omega)]
  have h0 : 32 + i < 64 := by omega
  by_cases h : n + i < 32
  · have h1 : i < 32 - n := by omega
    have h2 : 32 + i < 64 - n := by omega
    have h3 : 32 + (n + i) = n + (32 + i) := by omega
    simp [h, h0, h1, h2, h3]
  · have h1 : ¬ i < 32 - n := by omega
    have h2 : ¬ 32 + i < 64 - n := by omega
    have h3 : i - (32 - n) = 32 + i - (64 - n) := by omega
    simp [h, h0, h1, h2, h3]

private theorem rorLowBig (v : BitVec 64) (n : Nat) (hn : 32 ≤ n ∧ n < 64) :
    (v.setWidth 32 <<< (64 - n)) ||| ((v >>> (32 : Nat)).setWidth 32 >>> (n - 32)) =
      (v.rotateRight n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_rotateRight, hi, Nat.mod_eq_of_lt hn.2]
  by_cases h : i < 64 - n
  · have h1 : n - 32 + i < 32 := by omega
    have h2 : 32 + (n - 32 + i) = n + i := by omega
    simp [h, h1, h2]
  · have h1 : ¬ n - 32 + i < 32 := by omega
    simp [h, h1, show i < 64 by omega]

private theorem rorHighBig (v : BitVec 64) (n : Nat) (hn : 32 ≤ n ∧ n < 64) :
    ((v >>> (32 : Nat)).setWidth 32 <<< (64 - n)) ||| (v.setWidth 32 >>> (n - 32)) =
      ((v.rotateRight n) >>> (32 : Nat)).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth,
    hi, Nat.mod_eq_of_lt hn.2,
    show ¬ 32 + i < 64 - n by omega, show 32 + i < 64 by omega]
  have hindex : 32 + i - (64 - n) < 64 := by omega
  rw [← BitVec.getLsbD_eq_getElem hindex]
  by_cases h : i < 64 - n
  · have h1 : n - 32 + i < 32 := by omega
    have h2 : n - 32 + i = 32 + i - (64 - n) := by omega
    simp [h, h2, show 32 + i - (64 - n) < 32 by omega]
  · have h1 : ¬ n - 32 + i < 32 := by omega
    have h2 : 32 + (i - (64 - n)) = 32 + i - (64 - n) := by omega
    simp [h, h1, h2]

private theorem lsrLowBig (v : BitVec 64) (n : Nat) (hn : 32 ≤ n) :
    (v >>> (32 : Nat)).setWidth 32 >>> (n - 32) = (v >>> n).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_setWidth, hi]
  have h1 : (n - 32 + i < 32) ↔ (n + i < 64) := by omega
  have h2 : 32 + (n - 32 + i) = n + i := by omega
  by_cases h : n + i < 64
  · simp [h, h1, h2]
  · simp [h, h1, BitVec.getLsbD_of_ge v (n + i) (by omega)]

private theorem lslLowBig (v : BitVec 64) (n : Nat) (hn : 32 ≤ n) :
    (v <<< n).setWidth 32 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi, show i < n by omega]

private theorem lsrHighBig (v : BitVec 64) (n : Nat) (hn : 32 ≤ n) :
    ((v >>> n) >>> (32 : Nat)).setWidth 32 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [BitVec.getLsbD_ushiftRight, hi,
    BitVec.getLsbD_of_ge v (n + (32 + i)) (by omega)]

private theorem asrHighBig (v : BitVec 64) (n : Nat) (hn : 32 ≤ n) :
    ((v >>> (32 : Nat)).setWidth 32).sshiftRight 32 =
      ((v.sshiftRight n) >>> (32 : Nat)).setWidth 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hmsb : ((v >>> (32 : Nat)).setWidth 32).msb = v.msb := by
    simp [BitVec.msb_eq_getLsbD_last]
  simp only [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, hmsb]
  simp [hi, show ¬ 32 ≤ i by omega, show ¬ 64 ≤ 32 + i by omega,
    show ¬ 32 + i < 32 by omega, show ¬ n + (32 + i) < 64 by omega]


/-- The 32-bit word program computes the full HOL Word64 shift result. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml"
  "evaluate_WordShift64_on_32" (fmap_as_finite_support := [fpRegs, store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWordShift64On32 {width : Nat} [NeZero width] {C F : Type} (sh : Shift) (n : Nat) (v : BitVec 64)
    (t : WordSemStateFiniteExact width C F) (locals : Spt (WordLocW width)) (hwidth : width = 32) :
  WordSemStateFiniteExact.evaluate (wordShift64On32 sh n)
      {t with locals := (sptInsert 13 (.word (holWordExtract 31 0 v width))
        (sptInsert 11 (.word (holWordExtract 63 32 v width)) locals))} =
    (none, {t with locals := (sptInsert 31 (.word (holWordExtract 63 32 (shiftLookup sh v n) width))
       (sptInsert 33 (.word (holWordExtract 31 0 (shiftLookup sh v n) width))
         (sptInsert 13 (.word (holWordExtract 31 0 v width))
           (sptInsert 11 (.word (holWordExtract 63 32 v width)) locals))))}) := by
  subst width
  have high (v : BitVec 64) : holWordExtract 63 32 v 32 = (v >>> (32 : Nat)).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  have low (v : BitVec 64) : holWordExtract 31 0 v 32 = v.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  cases sh with
  | lsl =>
    by_cases hn : n < 32
    · simp [wordShift64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, wordExpShiftVar, wordOpHOL, wordOp, theWords,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, shiftLookup, hn, high, low,
        OrOp.or, lslHighSmall v n hn]
    · have hn32 : 32 ≤ n := by omega
      simp [wordShift64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, wordExpShiftVar,         sptLookup_sptInsert_same, sptLookup_sptInsert_ne, shiftLookup, hn, high, low,
        lslHighBig v n hn32, lslLowBig v n hn32]
  | lsr =>
    by_cases hn : n < 32
    · simp [wordShift64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, wordExpShiftVar, wordOpHOL, wordOp, theWords,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, shiftLookup, hn, high, low,
        OrOp.or, lsrLowSmall v n hn, lsrHigh v n]
    · have hn32 : 32 ≤ n := by omega
      simp [wordShift64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, wordExpShiftVar,         sptLookup_sptInsert_same, sptLookup_sptInsert_ne, shiftLookup, hn, high, low,
        lsrLowBig v n hn32, lsrHighBig v n hn32]
  | asr =>
    by_cases hn : n < 32
    · simp [wordShift64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, wordExpShiftVar, wordOpHOL, wordOp, theWords,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, shiftLookup, hn, high, low,
        OrOp.or, lsrLowSmall v n hn, asrHigh v n, asrLowSmall v n hn]
    · have hn32 : 32 ≤ n := by omega
      simp [wordShift64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, wordExpShiftVar,         sptLookup_sptInsert_same, sptLookup_sptInsert_ne, shiftLookup, hn, high, low,
        asrLowBig v n hn32, asrHighBig v n hn32]
  | ror =>
    have hmod : n % 64 < 64 := Nat.mod_lt _ (by decide)
    by_cases hn : n % 64 < 32
    · simp [wordShift64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, wordExpShiftVar, wordOpHOL, wordOp, theWords,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, shiftLookup, hn, high, low,
        OrOp.or, rorLowSmall v (n % 64) hn, rorHighSmall v (n % 64) hn,
        BitVec.rotateRight_mod_eq_rotateRight]
    · have hn32 : 32 ≤ n % 64 := by omega
      simp [wordShift64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
        WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
        WordSemStateFiniteExact.fixClock, wordExpShiftVar, wordOpHOL, wordOp, theWords,
        sptLookup_sptInsert_same, sptLookup_sptInsert_ne, shiftLookup, hn, high, low,
        OrOp.or, rorLowBig v (n % 64) ⟨hn32, hmod⟩, rorHighBig v (n % 64) ⟨hn32, hmod⟩,
        BitVec.rotateRight_mod_eq_rotateRight]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

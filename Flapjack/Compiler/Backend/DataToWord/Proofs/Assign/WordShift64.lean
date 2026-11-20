module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.FpCommon
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Word64
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.Space
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.ShiftVar
@[expose] public section

/-! The 32-bit lowering of a 64-bit shift, following the HOL assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataToWord.Proofs
open Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL
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

private theorem shiftSource {C F : Type} (sh : Shift) (amount : Nat) (values : List DataSem.Value)
    (source resultState : DataSem.State C F) (result : DataSem.Value)
    (run : DataSem.doApp (.wordOp (.wordShift .w64 sh amount)) values source = .val (result, resultState)) :
    ∃ word next, values = [.word64 word] ∧ DataSem.consumeSpace 3 source = some next ∧
      result = .word64 (shift64Lookup sh word amount) ∧
      resultState = DataSem.doStack (.wordOp (.wordShift .w64 sh amount)) values
        (DataSem.doLimSafe next (.wordOp (.wordShift .w64 sh amount)) values) := by
  cases h : DataSem.consumeSpace 3 source with
  | none =>
    simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq, h] at run
  | some next =>
    cases values with
    | nil => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
        h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
    | cons value rest =>
      cases rest with
      | cons x xs => simp [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          h, DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral] at run
      | nil =>
        cases value <;> simp_all [DataSem.doApp, DataSem.doSpace, DataLang.opSpaceReset, DataSpace.opSpaceReq,
          DataSem.doAppAux, DataSem.applyNonFfi, DataSem.doWordApp, DataSem.doWordAppIntegral]


private theorem shiftHeaderOfSafe {width : Nat} [NeZero width] {C F : Type}
    (conf : DataToWord.Config) (source : DataSem.State C F)
    (target : WordSemStateFiniteExact width C F) (l1 l2 : Nat) (locs : List (Nat × Nat))
    (sh : Shift) (amount : Nat) (values : List DataSem.Value)
    (related : stateRel conf l1 l2 source target none locs)
    (safe : DataSem.limSafe source.limits (.wordOp (.wordShift .w64 sh amount)) values) :
    ∃ hd, encodeHeader (width := width) conf 3 (if width = 64 then 1 else 2) = some hd := by
  have good := related.2.2.2.2.2.2.1
  have limits := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have mem := related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨heap, limit, a, sp, sp1, gens, heapMem, _⟩ := mem
  have lenPos : 0 < conf.lenSize := by
    have h := heapMem.2.2.2.1
    omega
  have lenBound : conf.lenSize + 7 < width := heapMem.2.2.2.2.1
  have limitEq : source.limits.lengthLimit = conf.lenSize := limits.2.1
  rcases good with h | h <;> subst width
  · have safeLen : 1 < conf.lenSize := by
      simp [DataSem.limSafe, limitEq] at safe
      exact safe
    have countBound : 2 < 2 ^ conf.lenSize := by
      have h : 2 ^ 2 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    refine ⟨makeHeader conf (BitVec.ofNat 32 3) 2, ?_⟩
    simp [encodeHeader, countBound, show 3 < 2 ^ (32 - conf.lenSize - 2) by
      have h : 2 ^ 3 ≤ 2 ^ (32 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]
  · have countBound : 1 < 2 ^ conf.lenSize := by
      have h : 2 ^ 1 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    refine ⟨makeHeader conf (BitVec.ofNat 64 3) 1, ?_⟩
    simp [encodeHeader, countBound, show 3 < 2 ^ (64 - conf.lenSize - 2) by
      have h : 2 ^ 3 ≤ 2 ^ (64 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega]

private theorem shiftPrefix64 {C F : Type} (conf : Config) (sh : Shift) (amount arg : Nat)
    (target : WordSemStateFiniteExact 64 C F) (addr : BitVec 64) (word : BitVec 64)
    (real : target.wordExp (realAddr conf (adjustVar arg)) = some (.word addr))
    (domain : target.mdomain (addr + wordSemBytesInWord) = true)
    (load : target.memory (addr + wordSemBytesInWord) = .word word) :
    WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 3 (.load (.op .add [realAddr conf (adjustVar arg), .const wordSemBytesInWord])),
      .assign 3 (shiftVar sh 3 amount)]) target =
      (none, target.setVar 3 (.word (shiftLookup sh word amount))) := by
  simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
    WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.setVar,
    WordSemStateFiniteExact.fixClock, wordExpShiftVar, wordOpHOL, wordOp, theWords,
    real, domain, load, sptLookup_sptInsert_same, sptInsert_insert_shadow]

private theorem shiftPrefix32 {C F : Type} (conf : Config) (sh : Shift) (amount arg : Nat)
    (target : WordSemStateFiniteExact 32 C F) (addr : BitVec 32) (word : BitVec 64)
    (real : target.wordExp (realAddr conf (adjustVar arg)) = some (.word addr))
    (domain1 : target.mdomain (addr + wordSemBytesInWord) = true)
    (domain2 : target.mdomain (addr + 2 * wordSemBytesInWord) = true)
    (load1 : target.memory (addr + wordSemBytesInWord) = .word ((word >>> (32 : Nat)).setWidth 32))
    (load2 : target.memory (addr + 2 * wordSemBytesInWord) = .word (word.setWidth 32)) :
    WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 15 (realAddr conf (adjustVar arg)),
      .assign 11 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
      .assign 13 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)])),
      wordShift64On32 sh amount]) target =
      (none, (target.setVar 15 (.word addr)).setVar 11 (.word ((word >>> (32 : Nat)).setWidth 32))
        |>.setVar 13 (.word (word.setWidth 32))
        |>.setVar 33 (.word ((shiftLookup sh word amount).setWidth 32))
        |>.setVar 31 (.word (((shiftLookup sh word amount) >>> (32 : Nat)).setWidth 32))) := by
  simp only [BitVec.ofNat_eq_ofNat] at domain2 load2
  let mid := ((target.setVar 15 (.word addr)).setVar 11 (.word ((word >>> (32 : Nat)).setWidth 32))).setVar 13 (.word (word.setWidth 32))
  have loads : WordSemStateFiniteExact.evaluate (wordListSeq [
      .assign 15 (realAddr conf (adjustVar arg)),
      .assign 11 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
      .assign 13 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)]))]) target = (none, mid) := by
    simp [wordListSeq, WordSemStateFiniteExact.evaluate, WordSemStateFiniteExact.wordExp,
      WordSemStateFiniteExact.memLoad, WordSemStateFiniteExact.getVar,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock,
      wordOpHOL, wordOp, theWords, real, domain1, domain2, load1, load2,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne, mid]
  have shiftRun := evaluateWordShift64On32 sh amount word (target.setVar 15 (.word addr))
    (target.setVar 15 (.word addr)).locals rfl
  have high (v : BitVec 64) : holWordExtract 63 32 v 32 = (v >>> (32 : Nat)).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  have low (v : BitVec 64) : holWordExtract 31 0 v 32 = v.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  have joined := evalListAppend [
      .assign 15 (realAddr conf (adjustVar arg)),
      .assign 11 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
      .assign 13 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)]))]
      (wordShift64On32 sh amount) target mid loads
  rw [show WordSemStateFiniteExact.evaluate (wordShift64On32 sh amount) mid = _ by
    simpa [mid, WordSemStateFiniteExact.setVar, high, low] using shiftRun] at joined
  simpa [WordSemStateFiniteExact.setVar] using joined

/-- A Word64 shift satisfies the complete data-to-word assignment simulation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "assign_WordShiftW64"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem assignWordShift_correct {width : Nat} [NeZero width] {C F : Type}
    (conf : Flapjack.Compiler.Backend.DataToWord.Config) (n l l1 l2 dest : Nat) (op : Flapjack.Compiler.Backend.ClosLang.Op)
    (args : List Nat) (names : Option NumSet)
    (source cut resultState : Flapjack.Compiler.Backend.DataSem.State C F) (target : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (values : List Flapjack.Compiler.Backend.DataSem.Value) (result : Flapjack.Compiler.Backend.DataSem.Value)
    (opIs : ∃ sh amount, op = .wordOp (.wordShift .w64 sh amount)) (related : stateRel conf l1 l2 source target none locs)
    (validNames : DataLang.opRequiresNames op ≠ names.isNone)
    (cutEq : DataSem.cutStateOpt names source = some cut)
    (argsEq : DataSem.getVars args source.locals = some values) (_depth : target.termdep > 1)
    (run : DataSem.doApp op values cut = .val (result, resultState)) :
    ∃ q r, WordSemStateFiniteExact.evaluate (compileAssign conf n l dest op args names).1 target = (q,r) ∧
      (q = some .notEnoughSpace → r.ffi = target.ffi ∧ optionLe r.stackMax resultState.stackMax ∧
        (conf.gcKind ≠ .none → resultState.safeForSpace = false)) ∧
      (q ≠ some .notEnoughSpace → stateRel conf l1 l2 (DataSem.setVar dest result resultState) r none locs ∧ q = none) := by
  obtain ⟨sh, amount, rfl⟩ := opIs
  cases names with
  | some names => simp [DataLang.opRequiresNames, DataLang.opSpaceReset] at validNames
  | none =>
    have cutIsSource : cut = source := by simpa [DataSem.cutStateOpt] using cutEq.symm
    subst cut
    obtain ⟨word, next, valuesEq, spaceEq, resultEq, stateEq⟩ := shiftSource sh amount values source resultState result run
    subst values
    subst result
    subst resultState
    have shiftEq : shiftLookup sh word amount = shift64Lookup sh word amount := by
      cases sh <;> rfl
    have argLen := DataSpace.getVars_length args source.locals [.word64 word] argsEq
    cases args with
    | nil => simp at argLen
    | cons arg rest =>
      cases rest with
      | cons x xs => simp at argLen
      | nil =>
        have nextEq : next = { source with space := source.space - 3 } := by
          unfold DataSem.consumeSpace at spaceEq
          split at spaceEq <;> simp_all
        subst next
        have nextRel : stateRel conf l1 l2
            (DataSem.doStack (.wordOp (.wordShift .w64 sh amount)) [.word64 word]
              (DataSem.doLimSafe source (.wordOp (.wordShift .w64 sh amount)) [.word64 word])) target none locs :=
          stateRel_doStack conf l1 l2 _ target locs _ _
            (stateRel_doLimSafe conf l1 l2 source target locs _ _ related)
        have lenEq : (if width < 64 then 2 else 1) = (if width = 64 then 1 else 2) := by
          rcases related.2.2.2.2.2.2.1 with h | h <;> subst width <;> decide
        cases header : encodeHeader (width := width) conf 3 (if width = 64 then 1 else 2) with
        | some hd =>
          obtain ⟨words, getWords, lengthEq⟩ :=
            stateRel_getVars conf l1 l2 source target locs [arg] [.word64 word] related argsEq
          cases words with
          | nil => simp at lengthEq
          | cons loc rest =>
            cases rest with
            | cons x xs => simp at lengthEq
            | nil =>
              let envs := [(theGlobal source.global, holFapply target.store .globals)] ++
                flatStack source.stack target.stack
              let locals := joinEnv source.locals (sptToAList (sptInter target.locals (adjustSet source.locals)))
              have roots := memoryRel_getVars conf target.be (holThe source.tstamps) source source.space
                target.store target.memory target.mdomain target envs [arg] [.word64 word] [loc] (by
                  refine ⟨?_, argsEq, getWords⟩
                  simpa [envs] using related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2)
              have good := related.2.2.2.2.2.2.1
              obtain ⟨index, addr, originalHeader, locEq, realAddrEq, domainHeader, headerWord,
                bit3, bit4, bit2, domainFirst, payload⟩ :=
                  memoryRel_word64Imp conf target.be (holThe source.tstamps) source.refs source.space
                    target.store target.memory target.mdomain word loc (locals ++ envs)
                    ⟨by simpa [locals, envs, List.append_assoc] using roots, good⟩
              have locRead : WordSemStateFiniteExact.getVar (adjustVar arg) target = some loc := by
                cases found : WordSemStateFiniteExact.getVar (adjustVar arg) target <;>
                  simp_all [WordSemStateFiniteExact.getVars]
              have pointerRead : WordSemStateFiniteExact.getVar (adjustVar arg) target =
                  some (.word (getAddr conf index (.word 0))) := by simpa [locEq] using locRead
              have realEval := Bignum.getRealAddr_lemma conf (adjustVar arg) target
                (getAddr conf index (.word 0)) addr
                ⟨related.2.2.2.2.2.2.2.1, good, pointerRead, realAddrEq⟩
              have spaceEnough : 3 ≤ source.space := by
                unfold DataSem.consumeSpace at spaceEq
                split at spaceEq <;> simp_all
              rcases good with width32 | width64
              · subst width
                simp only [show 32 < 64 by decide, ↓reduceIte] at payload
                obtain ⟨payloadHigh, domainSecond, payloadLow, decoded, originalHeaderEq⟩ := payload
                let resultWord := shiftLookup sh word amount
                let pre := WordSemStateFiniteExact.setVar 31 (.word ((resultWord >>> (32 : Nat)).setWidth 32))
                  (WordSemStateFiniteExact.setVar 33 (.word (resultWord.setWidth 32))
                    (WordSemStateFiniteExact.setVar 13 (.word (word.setWidth 32))
                      (WordSemStateFiniteExact.setVar 11 (.word ((word >>> (32 : Nat)).setWidth 32))
                        (WordSemStateFiniteExact.setVar 15 (.word addr) target))))
                have prefixEval := shiftPrefix32 conf sh amount arg target addr word realEval
                  (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domainFirst)
                  (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domainSecond)
                  (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadHigh)
                  (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadLow)
                have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                    pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
                  simpa [pre, WordSemStateFiniteExact.setVar,
                    joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
                      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                have preLow : pre.getVar 33 = some (.word (resultWord.setWidth 32)) := by
                  simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_same, sptLookup_sptInsert_ne]
                have preHigh : pre.getVar 31 = some (.word ((resultWord >>> (32 : Nat)).setWidth 32)) := by
                  simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_same]
                have prePresent : ∀ k, (sptLookup k source.locals).isSome →
                    (sptLookup (adjustVar k) pre.locals).isSome := by
                  intro k present
                  have odd31 : adjustVar k ≠ 31 := by simp [adjustVar]; omega
                  have odd33 : adjustVar k ≠ 33 := by simp [adjustVar]; omega
                  have odd11 : adjustVar k ≠ 11 := by simp [adjustVar]; omega
                  have odd13 : adjustVar k ≠ 13 := by simp [adjustVar]; omega
                  have odd15 : adjustVar k ≠ 15 := by simp [adjustVar]; omega
                  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := related
                  simpa [pre, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_ne _ _ _ _ odd31, sptLookup_sptInsert_ne _ _ _ _ odd33,
                    sptLookup_sptInsert_ne _ _ _ _ odd11, sptLookup_sptInsert_ne _ _ _ _ odd13,
                    sptLookup_sptInsert_ne _ _ _ _ odd15] using presentOld k present
                have writeRun := evaluateWriteWord64On32 (β := PUnit) conf target.be (holThe source.tstamps)
                  source.space source.refs pre source.locals envs 33 31 dest resultWord hd
                  preHeap preLow preHigh related.2.2.2.2.2.2.2.1 (by decide) (by decide) (by omega) rfl
                  (by simpa using header) prePresent
                obtain ⟨nf, memory, locals1, unused, writeEval, writeHeap, localsPreserved,
                  destPresent, zeroEq⟩ := writeRun
                have finalHeap : memoryRel conf target.be (holThe source.tstamps) source.refs
                    (source.space - 3) (target.store.update (.nextFree, nf)) memory target.mdomain
                    (joinEnvLocals (sptInsert dest (.word64 resultWord) source.locals) locals1 ++ envs) := by
                  simpa [pre, WordSemStateFiniteExact.setVar] using writeHeap
                let nextSource := DataSem.doStack (.wordOp (.wordShift .w64 sh amount)) [.word64 word]
                  (DataSem.doLimSafe source (.wordOp (.wordShift .w64 sh amount)) [.word64 word])
                have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
                  nextSource target locs (.word64 resultWord) nf memory locals1 pre.fpRegs nextRel
                  (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
                  destPresent
                  (by simpa [pre, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_ne] using zeroEq)
                  (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe, envs] using finalHeap)
                have header32 : encodeHeader (width := 32) conf 3 2 = some hd := by simpa using header
                have seqRun := evalListAppend [
                  .assign 15 (realAddr conf (adjustVar arg)),
                  .assign 11 (.load (.op .add [.var 15, .const wordSemBytesInWord])),
                  .assign 13 (.load (.op .add [.var 15, .const (2 * wordSemBytesInWord)])),
                  wordShift64On32 sh amount] (writeWord64On32 conf hd dest 33 31) target pre
                  (by simpa [pre, resultWord] using prefixEval)
                rw [writeEval] at seqRun
                refine ⟨none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1}, ?_, ?_, ?_⟩
                · simpa [compileAssign, arg1, assignWordShiftW64, loadWord64, header32] using seqRun
                · simp
                · intro _
                  refine ⟨?_, rfl⟩
                  simpa [nextSource, resultWord, shiftEq, pre, DataSem.doStack, DataSem.doLimSafe,
                    WordSemStateFiniteExact.setVar] using finalRel
              · subst width
                simp only [show ¬ 64 < 64 by decide, ↓reduceIte] at payload
                obtain ⟨payloadWord, decoded, originalHeaderEq⟩ := payload
                let resultWord := shiftLookup sh word amount
                let pre := WordSemStateFiniteExact.setVar 3 (.word resultWord) target
                have prefixEval := shiftPrefix64 conf sh amount arg target addr word realEval
                  (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using domainFirst)
                  (by simpa [StackRemove.bytesInWord, wordSemBytesInWord] using payloadWord)
                have preHeap : memoryRel conf target.be (holThe source.tstamps) source.refs source.space
                    pre.store pre.memory pre.mdomain (joinEnvLocals source.locals pre.locals ++ envs) := by
                  simpa [pre, WordSemStateFiniteExact.setVar,
                    joinEnvLocals_insertOdd, inter_insertOdd_adjustSet, envs, joinEnvLocals] using
                      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
                have preRead : pre.getVar 3 = some (.word resultWord) := by
                  simp [pre, WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_same]
                have prePresent : ∀ k, (sptLookup k source.locals).isSome →
                    (sptLookup (adjustVar k) pre.locals).isSome := by
                  intro k present
                  have odd : adjustVar k ≠ 3 := by simp [adjustVar]
                  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, presentOld, _⟩ := related
                  simpa [pre, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_ne _ _ _ _ odd] using presentOld k present
                have writeRun := evaluateWriteWord64 (β := PUnit) conf target.be (holThe source.tstamps)
                  source.space source.refs pre source.locals envs 3 dest resultWord hd
                  preHeap preRead related.2.2.2.2.2.2.2.1 (by decide) (by omega) rfl
                  (by simpa using header) prePresent
                obtain ⟨nf, memory, locals1, unused, writeEval, writeHeap, localsPreserved,
                  destPresent, zeroEq⟩ := writeRun
                have smallerHeap : memoryRel conf target.be (holThe source.tstamps) source.refs
                    (source.space - 3) (target.store.update (.nextFree, nf)) memory target.mdomain
                    (joinEnvLocals (sptInsert dest (.word64 resultWord) source.locals) locals1 ++ envs) := by
                  apply memoryRel_lessSpace conf target.be (holThe source.tstamps) source.refs
                    (source.space - 2) (source.space - 3) _ _ _ _
                  refine ⟨?_, by omega⟩
                  simpa [pre, WordSemStateFiniteExact.setVar] using writeHeap
                let nextSource := DataSem.doStack (.wordOp (.wordShift .w64 sh amount)) [.word64 word]
                  (DataSem.doLimSafe source (.wordOp (.wordShift .w64 sh amount)) [.word64 word])
                have finalRel := stateRelNextFreeResult conf l1 l2 dest (source.space - 3)
                  nextSource target locs (.word64 resultWord) nf memory locals1 pre.fpRegs nextRel
                  (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe] using localsPreserved)
                  destPresent
                  (by simpa [pre, WordSemStateFiniteExact.setVar,
                    sptLookup_sptInsert_ne] using zeroEq)
                  (by simpa [nextSource, DataSem.doStack, DataSem.doLimSafe, envs] using smallerHeap)
                have header64 : encodeHeader (width := 64) conf 3 1 = some hd := by simpa using header
                have seqRun := evalListAppend [
                  .assign 3 (.load (.op .add [realAddr conf (adjustVar arg), .const wordSemBytesInWord])),
                  .assign 3 (shiftVar sh 3 amount)] (writeWord64 conf hd dest 3) target pre
                  (by simpa [pre, resultWord] using prefixEval)
                rw [writeEval] at seqRun
                refine ⟨none, {pre with store := pre.store.update (.nextFree, nf), memory := memory, locals := locals1}, ?_, ?_, ?_⟩
                · simpa [compileAssign, arg1, assignWordShiftW64, loadWord64, header64] using seqRun
                · simp
                · intro _
                  refine ⟨?_, rfl⟩
                  simpa [nextSource, resultWord, shiftEq, pre, DataSem.doStack, DataSem.doLimSafe,
                    WordSemStateFiniteExact.setVar] using finalRel
        | none =>
          obtain ⟨out, outEval, outFfi, targetFfi, outMax⟩ := evaluateGiveUp2 conf l1 l2 source target locs related
          have noSafe : ¬ DataSem.limSafe source.limits (.wordOp (.wordShift .w64 sh amount)) [.word64 word] := by
            intro safe
            obtain ⟨hd, encoded⟩ := shiftHeaderOfSafe conf source target l1 l2 locs sh amount [.word64 word] related safe
            rw [header] at encoded
            contradiction
          refine ⟨some .notEnoughSpace, out, ?_, ?_, ?_⟩
          · simpa [compileAssign, arg1, assignWordShiftW64, lenEq, header] using outEval
          · intro _
            refine ⟨outFfi.trans targetFfi.symm, ?_, ?_⟩
            · have targetBound := nextRel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
              apply BackendProps.optionLe_trans _ _ _ ⟨outMax, ?_⟩
              simpa [DataSem.doStack, DataSem.doLimSafe] using targetBound
            · intro _
              simp [DataSem.doStack, DataSem.doLimSafe, noSafe]
          · simp

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

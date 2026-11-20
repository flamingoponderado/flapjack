module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.WordShift64
@[expose] public section

/-! Word64 binary-operation prerequisites for the data-to-word assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.BackendProps
open Flapjack.SemanticPrimitivesHOL

namespace Op64Witness
/-- Canonical finite-map roundtrip for the target word state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end Op64Witness
set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

/-- The HOL 32-bit header conditions make the two-word header encodable. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "IMP_encode_header_NOT_NONE"
  (words_as_type_indexed_bitvec)]
theorem encodeHeader32NotNone {width : Nat} [NeZero width] (conf : Config)
    (h : width = 32 ∧ 1 < conf.lenSize ∧ 1 < 30 - conf.lenSize) :
    encodeHeader conf 3 2 ≠ (none : Option (BitVec width)) := by
  obtain ⟨rfl, lenLower, lenUpper⟩ := h
  have lenBound : 2 < 2 ^ conf.lenSize := by
    have p : 2 ^ 2 ≤ 2 ^ conf.lenSize := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have tagBound : 3 < 2 ^ (32 - conf.lenSize - 2) := by
    have p : 2 ^ 2 ≤ 2 ^ (32 - conf.lenSize - 2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  simp [encodeHeader, lenBound, tagBound]

private theorem addLow (a b : BitVec 64) :
    (wordAddCarryHOL (a.setWidth 32) (b.setWidth 32) 0).1 = (a+b).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [wordAddCarryHOL, BitVec.toNat_add, BitVec.toNat_setWidth, Nat.add_mod]
private theorem addHigh (a b : BitVec 64) :
    (wordAddCarryHOL ((a >>> (32 : Nat)).setWidth 32) ((b >>> (32 : Nat)).setWidth 32)
      (wordAddCarryHOL (a.setWidth 32) (b.setWidth 32) 0).2).1 = ((a+b) >>> (32 : Nat)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [wordAddCarryHOL, BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight]
  simp only [Nat.shiftRight_eq_div_pow]
  norm_num only [Nat.reducePow]
  rw [show 18446744073709551616 = 4294967296 * 4294967296 by decide,
    Nat.mod_mul_right_div_self]
  rw [Nat.add_div (by decide : 0 < 4294967296)]
  simp [Nat.add_mod]

  split_ifs <;> simp_all
  all_goals omega

private theorem subLow (a b : BitVec 64) :
    (wordAddCarryHOL (a.setWidth 32) (~~~(b.setWidth 32)) 1).1 = (a-b).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [wordAddCarryHOL, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_not]
  omega
private theorem subHigh (a b : BitVec 64) :
    (wordAddCarryHOL ((a >>> (32 : Nat)).setWidth 32) (~~~((b >>> (32 : Nat)).setWidth 32))
      (wordAddCarryHOL (a.setWidth 32) (~~~(b.setWidth 32)) 1).2).1 =
      ((a-b) >>> (32 : Nat)).setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [wordAddCarryHOL, BitVec.toNat_sub, BitVec.toNat_setWidth, BitVec.toNat_not,
    BitVec.toNat_ushiftRight]
  simp only [Nat.shiftRight_eq_div_pow]
  norm_num only [Nat.reducePow]
  rw [show 18446744073709551616 = 4294967296 * 4294967296 by decide,
    Nat.mod_mul_right_div_self]
  rw [Nat.add_div (by decide : 0 < 4294967296)]
  simp only [Nat.mod_mod]
  have ha := a.isLt
  have hb := b.isLt
  norm_num only [Nat.reducePow] at ha hb
  split_ifs <;> omega

/-- Evaluate the two-word lowering for every Word64 operation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml"
  "evaluate_WordOp64_on_32" (fmap_as_finite_support := [fpRegs, store])
  (words_as_type_indexed_bitvec)]
theorem evaluateWordOp64On32 {width : Nat} [NeZero width] {C F : Type} (op : BackendCommon.Opw)
    (a b : BitVec 64) (t : WordSemStateFiniteExact width C F) (locals : Spt (WordLocW width)) (hwidth : width = 32) :
    ∃ w27 w29 : WordLocW width,
      WordSemStateFiniteExact.evaluate (wordOp64On32 op)
        {t with locals := (sptInsert 23 (.word (holWordExtract 31 0 b width))
          (sptInsert 21 (.word (holWordExtract 63 32 b width))
            (sptInsert 13 (.word (holWordExtract 31 0 a width))
              (sptInsert 11 (.word (holWordExtract 63 32 a width)) locals))))} =
      (none, {t with locals := (sptInsert 31 (.word (holWordExtract 63 32 (ClosSem.applyWordOp op a b) width))
        (sptInsert 33 (.word (holWordExtract 31 0 (ClosSem.applyWordOp op a b) width))
          (sptInsert 27 w27 (sptInsert 29 w29
            (sptInsert 23 (.word (holWordExtract 31 0 b width))
              (sptInsert 21 (.word (holWordExtract 63 32 b width))
                (sptInsert 13 (.word (holWordExtract 31 0 a width))
                  (sptInsert 11 (.word (holWordExtract 63 32 a width)) locals))))))))}) := by
  subst width
  have high (v : BitVec 64) : holWordExtract 63 32 v 32 = (v >>> (32 : Nat)).setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  have low (v : BitVec 64) : holWordExtract 31 0 v 32 = v.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [holWordExtract, BitVec.toNat_setWidth]
  have andOnes (v : BitVec 32) : v &&& (4294967295 : BitVec 32) = v := by bv_decide
  simp only [BitVec.ofNat_eq_ofNat] at andOnes
  cases op with
  | andw | orw | xor =>
    refine ⟨.word 0, .word 0, ?_⟩
    simp [wordOp64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.setVar,
      WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.getVar,
      wordOpHOL, wordOp, theWords, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
      ClosSem.applyWordOp, high, low, AndOp.and, OrOp.or,
      BitVec.ushiftRight_and_distrib, BitVec.ushiftRight_or_distrib,
      BitVec.ushiftRight_xor_distrib, andOnes, sptInsert_swap 27 29 _ _ _ (by decide)]
  | add =>
    let carry1 := (wordAddCarryHOL (a.setWidth 32) (b.setWidth 32) (0 : BitVec 32)).2
    let carry2 := (wordAddCarryHOL ((a >>> (32 : Nat)).setWidth 32) ((b >>> (32 : Nat)).setWidth 32) carry1).2
    refine ⟨.word 0, .word carry2, ?_⟩
    simp [wordOp64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.getVar,
      sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
      ClosSem.applyWordOp, high, low, carry1, carry2, sptInsert_insert_shadow,
      sptInsert_swap 29 31 _ _ _ (by decide), sptInsert_swap 29 33 _ _ _ (by decide),
      sptInsert_swap 29 27 _ _ _ (by decide)]
    have lo := addLow a b
    have hi := addHigh a b
    simp only [BitVec.ofNat_eq_ofNat] at lo hi
    simp [lo, hi]

  | sub =>
    let carry1 := (wordAddCarryHOL (a.setWidth 32) (~~~(b.setWidth 32)) (1 : BitVec 32)).2
    let carry2 := (wordAddCarryHOL ((a >>> (32 : Nat)).setWidth 32) (~~~((b >>> (32 : Nat)).setWidth 32)) carry1).2
    refine ⟨.word (~~~((b >>> (32 : Nat)).setWidth 32)), .word carry2, ?_⟩
    simp [wordOp64On32, wordListSeq, WordSemStateFiniteExact.evaluate,
      WordSemStateFiniteExact.wordExp, WordSemStateFiniteExact.inst, WordSemStateFiniteExact.getVars,
      WordSemStateFiniteExact.setVar, WordSemStateFiniteExact.fixClock, WordSemStateFiniteExact.getVar,
      wordOpHOL, wordOp, theWords, sptLookup_sptInsert_same, sptLookup_sptInsert_ne,
      ClosSem.applyWordOp, high, low, carry1, carry2, sptInsert_insert_shadow,
      sptInsert_swap 29 31 _ _ _ (by decide), sptInsert_swap 29 33 _ _ _ (by decide),
      sptInsert_swap 29 27 _ _ _ (by decide), sptInsert_swap 27 33 _ _ _ (by decide)]
    have xorOnes (v : BitVec 32) : (4294967295 : BitVec 32) ^^^ v = ~~~v := by bv_decide
    have lo := subLow a b
    have hi := subHigh a b
    simp only [BitVec.ofNat_eq_ofNat] at xorOnes lo hi
    simp [xorOnes, lo, hi]


end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.StateRel
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BignumImp
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberConst
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum.RealAddress
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.WordLemmas
public import Flapjack.Compiler.Backend.Semantics.WordSem.Evaluate

@[expose] public section

/-! Size bound on the digits of a related source integer. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord
open Flapjack.Compiler.Backend.DataToWord.Proofs.Gc Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

namespace NumSizeWitness
/-- Canonical finite-map roundtrip for the word-semantics state. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width] {C F : Type} :
    (∀ (state : WordSemStateBroad width C F) (h : state.FiniteSupport),
      (WordSemStateBroad.ofBroad state h).toBroad = state) ∧
    (∀ state : WordSemStateFiniteExact width C F,
      WordSemStateBroad.ofBroad state.toBroad state.toBroad_finiteSupport = state) :=
  WordSemStateExact.holFmapAsFiniteSupportWitness
end NumSizeWitness

private theorem n2mw_length_le_one {width : Nat} [NeZero width] (n : Nat) (h : n < 2 ^ width) :
    (Misc.Multiword.n2mw n : List (BitVec width)).length ≤ 1 := by
  rw [Misc.Multiword.n2mw]
  split
  · simp
  · rw [Nat.div_eq_of_lt h, Misc.Multiword.n2mw]; simp

/-- A related source integer has fewer digits than a sixteenth of the word range. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml"
  "state_rel_IMP_num_size_limit" (fmap_as_finite_support := [fpRegs, store])
  (words_as_type_indexed_bitvec)]
theorem stateRel_imp_numSizeLimit {width : Nat} [NeZero width] {C F : Type}
    (c : Config) (l1 l2 : Nat) (s : DataSem.State C F) (t : WordSemStateFiniteExact width C F)
    (locs : List (Nat × Nat)) (k : Nat) (i : Int) :
    stateRel c l1 l2 s t none locs ∧ DataSem.getVar k s.locals = some (.number i) →
      (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length < 2 ^ width / 16 := by
  rintro ⟨rel, found⟩
  obtain ⟨w, hw⟩ := stateRel_getVar c l1 l2 s t none locs k _ rel found
  have good : goodDimindex width := rel.2.2.2.2.2.2.1
  have mem := rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have m2 := memoryRel_lookup c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain
    s.locals t.locals ([(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack)
    k (.number i) w ⟨by simpa [List.append_assoc] using mem, found, hw⟩
  have w16 : 2 ^ width / 16 = 2 ^ (width - 4) := by
    rw [show 16 = 2 ^ 4 by rfl, Nat.pow_div (by rcases good with h | h <;> omega) (by decide)]
  simp only [Misc.Multiword.i2mw]
  by_cases small : smallInt width i
  · have lt : i.natAbs < 2 ^ width := by
      obtain ⟨lo, hi⟩ := small
      rw [Int.ofNat_eq_natCast] at lo hi
      have : 2 ^ width / 8 ≤ 2 ^ width := Nat.div_le_self _ _
      omega
    have := n2mw_length_le_one i.natAbs lt
    rw [w16]
    have : 2 ≤ 2 ^ (width - 4) := by
      rcases good with h | h <;> subst h <;> decide
    omega
  · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hlen, _⟩ :=
      memoryRel_number_bignumImp_alt c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
        t.mdomain i w _ ⟨m2, small, good⟩
    rw [w16]; exact hlen

private theorem n2mw_length_one {width : Nat} [NeZero width] (n : Nat) (h : n < 2 ^ width)
    (ne : n ≠ 0) : (Misc.Multiword.n2mw n : List (BitVec width)).length = 1 := by
  rw [Misc.Multiword.n2mw, if_neg ne, Nat.div_eq_of_lt h, Misc.Multiword.n2mw]; simp

/-- Adding the digit count of a related integer to register 1. The evaluator
inherits the real-model assumption in `docs/SOUNDNESS.md` item 8. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "evaluate_AddNumSize"
  (fmap_as_finite_support := [fpRegs, store]) (words_as_type_indexed_bitvec)]
theorem evaluateAddNumSize {width : Nat} [NeZero width] {C F : Type} :
    ∀ (src : Nat) (c : Config) (l1 l2 : Nat) (s : DataSem.State C F)
      (t : WordSemStateFiniteExact width C F) (locs : List (Nat × Nat)) (i : Int)
      (w : BitVec width),
      stateRel c l1 l2 s t none locs ∧ DataSem.getVar src s.locals = some (.number i) →
      WordSemStateFiniteExact.evaluate (addNumSize c src) (t.setVar 1 (.word w)) =
        (none, t.setVar 1 (.word (w + BitVec.ofNat width
          (4 * (Misc.Multiword.i2mw i : Bool × List (BitVec width)).2.length)))) := by
  intro src c l1 l2 s t locs i w ⟨rel, found⟩
  obtain ⟨wv, hw⟩ := stateRel_getVar c l1 l2 s t none locs src _ rel found
  have good : goodDimindex width := rel.2.2.2.2.2.2.1
  have shiftLt : shiftLength c < width := rel.2.2.2.2.2.2.2.1
  have mem := rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have m2 := memoryRel_lookup c t.be (holThe s.tstamps) s.refs s.space t.store t.memory t.mdomain
    s.locals t.locals ([(theGlobal s.global, holFapply t.store .globals)] ++ flatStack s.stack t.stack)
    src (.number i) wv ⟨by simpa [List.append_assoc] using mem, found, hw⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, _, _, lenNe, lenLt, _⟩, _⟩ := id m2
  obtain ⟨w4, rfl, bit⟩ := memoryRel_anyNumberImp c t.be (holThe s.tstamps) s.refs s.space t.store
    t.memory t.mdomain i _ _ ⟨good, m2⟩
  have wpos : 32 ≤ width := by rcases good with h | h <;> omega
  have hr : sptLookup (adjustVar src) (t.setVar 1 (.word w)).locals = some (.word w4) := by
    simp [WordSemStateFiniteExact.setVar, adjustVar, sptLookup_sptInsert_ne]
    exact hw
  have test0 := memoryRel_numberConstTest c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
    t.mdomain i 0 w4 _ ⟨m2, good⟩
  have small0 : smallInt width 0 := by
    have : 0 < 2 ^ width / 8 := Nat.div_pos (by
      calc 8 = 2 ^ 3 := rfl
        _ ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)) (by decide)
    unfold smallInt
    rw [Int.ofNat_eq_natCast]
    constructor <;> omega
  rw [if_pos small0] at test0
  have sn0 : (smallnum 0 : BitVec width) = 0 := by simp [smallnum]
  rw [sn0] at test0
  by_cases hz : w4 = 0
  · subst hz
    have i0 : i = 0 := test0.1 rfl
    subst i0
    rw [addNumSize, WordSemStateFiniteExact.evaluate]
    simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.getVarImm, hr, wordSemWordCmp,
      Compiler.Encoders.Asm.wordCmpHOL, WordSemStateFiniteExact.evaluate, Misc.Multiword.i2mw,
      Misc.Multiword.n2mw]
  · have ine : i ≠ 0 := fun e => hz (test0.2 e).symm
    have hr' : WordSemStateFiniteExact.getVar (adjustVar src) (t.setVar 1 (.word w)) =
        some (.word w4) := hr
    by_cases hb : w4.getLsbD 0 = true
    · have nsmall : ¬ smallInt width i := bit.1 hb
      obtain ⟨_, w', x, a, hv, h1, hreal, hdom, hmem, _, _, _, _, _, _, _, _, _, _, hdec⟩ :=
        memoryRel_number_bignumImp_alt c t.be (holThe s.tstamps) s.refs s.space t.store t.memory
          t.mdomain i (.word w4) _ ⟨m2, nsmall, good⟩
      cases hv
      have ra := getRealAddr_lemma c (adjustVar src) (t.setVar 1 (.word w)) w4 a
        ⟨shiftLt, good, hr', by simpa [WordSemStateFiniteExact.setVar] using hreal⟩
      have hz' : (w4 == 0#width) = false := by simpa using hz
      have h1' : (AndOp.and w4 1#width == 0#width) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact h1
      have shAmt : (BitVec.ofNat width (width - c.lenSize)).toNat = width - c.lenSize :=
        Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) Nat.lt_two_pow_self)
      have two : (BitVec.ofNat width 2).toNat = 2 :=
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (by decide : 2 < 2 ^ 32)
          (Nat.pow_le_pow_right (by decide) wpos))
      have hexp : WordSemStateFiniteExact.wordExp (t.setVar 1 (.word w))
          (.op .add [.var 1, shiftN .lsl (shiftN .lsr (.load (realAddr c (adjustVar src)))
            (width - c.lenSize)) 2]) =
          some (.word (w + (x >>> (width - c.lenSize)) <<< (2 : Nat))) := by
        have hv1 : WordSemStateFiniteExact.getVar 1 (t.setVar 1 (.word w)) = some (.word w) := by
          simp [WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar,
            sptLookup_sptInsert_same]
        have hdom' : (t.setVar 1 (.word w)).mdomain a = true := hdom
        have hmem' : (t.setVar 1 (.word w)).memory a = .word x := hmem
        have nsh : ¬ (¬ width - c.lenSize = 0 ∧ width ≤ width - c.lenSize) := by omega
        have w2 : ¬ width ≤ 2 := by omega
        simp [WordSemStateFiniteExact.wordExp, ra, WordSemStateFiniteExact.memLoad, hv1, hdom',
          hmem', shiftN, wordShiftHOL, shAmt, two, theWords, wordOpHOL, wordOp, nsh, w2]
      rw [addNumSize, WordSemStateFiniteExact.evaluate]
      simp only [WordSemStateFiniteExact.getVarImm, hr', wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.ofNat_eq_ofNat, hz']
      rw [WordSemStateFiniteExact.evaluate]
      simp only [WordSemStateFiniteExact.getVarImm, hr', wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.ofNat_eq_ofNat, h1']
      rw [WordSemStateFiniteExact.evaluate, hexp]
      have hd : x >>> (width - c.lenSize) =
          BitVec.ofNat width (Misc.Multiword.n2mw i.natAbs : List (BitVec width)).length := hdec
      have sh2 (L : Nat) : (BitVec.ofNat width L) <<< (2 : Nat) = BitVec.ofNat width (4 * L) := by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
        rw [Nat.pow_two, Nat.mod_mul_mod, Nat.mul_comm]
      simp [Misc.Multiword.i2mw, hd, sh2, WordSemStateFiniteExact.setVar, sptInsert_insert_shadow]
    · have small : smallInt width i := by
        by_contra ns; exact hb (bit.2 ns)
      have lt : i.natAbs < 2 ^ width := by
        obtain ⟨lo, hi⟩ := small
        rw [Int.ofNat_eq_natCast] at lo hi
        have : 2 ^ width / 8 ≤ 2 ^ width := Nat.div_le_self _ _
        omega
      have len1 := n2mw_length_one (width := width) i.natAbs lt (by omega)
      have hz' : (w4 == 0#width) = false := by simpa using hz
      have h1' : (AndOp.and w4 1#width == 0#width) = true := by
        have := (word_index_test (n := 0) (w := w4) (by omega)).not
        simp only [hb, Bool.false_eq_true, not_not, Nat.pow_zero] at this
        simp only [beq_iff_eq]
        exact this.mp (by simp)
      rw [addNumSize, WordSemStateFiniteExact.evaluate]
      simp only [WordSemStateFiniteExact.getVarImm, hr', wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.ofNat_eq_ofNat, hz']
      rw [WordSemStateFiniteExact.evaluate]
      simp only [WordSemStateFiniteExact.getVarImm, hr', wordSemWordCmp,
        Compiler.Encoders.Asm.wordCmpHOL, BitVec.ofNat_eq_ofNat, h1']
      rw [WordSemStateFiniteExact.evaluate]
      simp [Misc.Multiword.i2mw, len1, WordSemStateFiniteExact.wordExp,
        WordSemStateFiniteExact.getVar, WordSemStateFiniteExact.setVar, sptLookup_sptInsert_same,
        theWords, wordOpHOL, wordOp, sptInsert_insert_shadow]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum

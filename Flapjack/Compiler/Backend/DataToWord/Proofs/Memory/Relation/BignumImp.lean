module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberHeader
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Misc.SetSep.Read

@[expose] public section

/-!
# Bignum layout facts from the memory relation

Counterparts of `memory_rel_Number_bignum_IMP_ALT` and
`memory_rel_Number_bignum_IMP` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. HOL
`Num (ABS i)` is `i.natAbs`, `word_bit k x` is written out as
`k ≤ width - 1 ∧ x.getLsbD k = true`, `bytes_in_word` is `wordSemBytesInWord`,
`fun2set (m,dm)` is `SetSep.fun2Set (m, fun a => dm a = true)` and
`x ∈ dm` is `dm x = true`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- Masking with a single power-of-two bit is zero exactly when that bit is
clear. Flapjack word infrastructure. -/
theorem and_twoPow_eq_zero_iff {width : Nat} [NeZero width] (x : BitVec width) (k : Nat) (hk : k < width) :
    (x &&& BitVec.ofNat width (2 ^ k)) = 0 ↔ x.getLsbD k = false := by
  constructor
  · intro h
    have := congrArg (fun v : BitVec width => v.getLsbD k) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_self, hk, decide_true,
      Bool.and_true] at this
    simpa using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
    by_cases e : k = j
    · subst e; simp [h]
    · simp [e]

/-- HOL `memory_rel_Number_bignum_IMP_ALT`. HOL's existential `y` (of an
independent type `β`) does not occur in the body; as every HOL type is
inhabited it is vacuous and omitted, as for the reviewed
`memory_rel_Number_bignum_header`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Number_bignum_IMP_ALT"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_number_bignumImp_alt {width : Nat} [NeZero width]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (i : Int) (v : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel c be ts refs sp st m dm ((.number i, v) :: vars) ∧ ¬ smallInt width i ∧ goodDimindex width →
      ∃ (ff : ((BitVec width × WordLocW width) → Prop) → Prop) (w x a : BitVec width),
        v = .word w ∧ (w &&& 1) ≠ 0 ∧ getRealAddr c st w = some a ∧ dm a = true ∧ m a = .word x ∧
        (x &&& 8) ≠ 0 ∧ (2 ≤ width - 1 ∧ x.getLsbD 2 = true) ∧ (3 ≤ width - 1 ∧ x.getLsbD 3 = true) ∧
        ((4 ≤ width - 1 ∧ x.getLsbD 4 = true) ↔ i < 0) ∧
        SetSep.star (Misc.wordList (a + wordSemBytesInWord)
            ((Misc.Multiword.n2mw i.natAbs : List (BitVec width)).map WordLocW.word)) ff
          (SetSep.fun2Set (m, fun p => dm p = true)) ∧
        dm (a + wordSemBytesInWord) = true ∧ m (a + wordSemBytesInWord) = .word (BitVec.ofNat width i.natAbs) ∧
        ((x &&& 16) = 0 ↔ 0 ≤ i) ∧
        (Misc.Multiword.n2mw i.natAbs : List (BitVec width)).length < 2 ^ (width - 4) ∧
        (Misc.Multiword.n2mw i.natAbs : List (BitVec width)).length < 2 ^ width ∧
        WordGcFunctions.decodeLength c x =
          BitVec.ofNat width (Misc.Multiword.n2mw i.natAbs : List (BitVec width)).length := by
  intro h
  obtain ⟨rel, large, good⟩ := h
  obtain ⟨w, a, ff, vEq, real, words⟩ :=
    memoryRel_bignumWords c be ts refs sp st m dm i v vars ⟨rel, large, good⟩
  simp only at words
  obtain ⟨header, inA, sep, lenBound, bit0, bit2, bit3, bit4, decode⟩ := words
  have wide : 32 ≤ width := by rcases good with rfl | rfl <;> omega
  have notZero : i.natAbs ≠ 0 := by
    intro z
    apply large
    have : i = 0 := Int.natAbs_eq_zero.mp z
    subst this
    rcases good with rfl | rfl <;> simp [smallInt]
  have digits : (Misc.Multiword.n2mw i.natAbs : List (BitVec width)) =
      BitVec.ofNat width (i.natAbs % 2 ^ width) :: Misc.Multiword.n2mw (i.natAbs / 2 ^ width) := by
    rw [Misc.Multiword.n2mw]
    simp [notZero]
  have first : BitVec.ofNat width (i.natAbs % 2 ^ width) = BitVec.ofNat width i.natAbs := by
    apply BitVec.eq_of_toNat_eq; simp
  have sepHead := sep
  rw [digits, List.map_cons, Misc.wordList, ← SetSep.starAssoc] at sepHead
  obtain ⟨headVal, headDom⟩ := SetSep.readFun2Set _ _ _ m (fun p => dm p = true) sepHead
  revert header bit2 bit3 bit4 decode
  generalize (makeHeader c _ _ : BitVec width) = x
  intro header bit2 bit3 bit4 decode
  refine ⟨ff, w, x, a, vEq, ?_, real, inA, header, ?_, ⟨by omega, bit2⟩, ⟨by omega, bit3⟩, ?_, sep,
    headDom, ?_, ?_, lenBound, ?_, decode⟩
  · intro z
    have := (and_twoPow_eq_zero_iff w 0 (by omega)).mp (by simpa using z)
    rw [bit0] at this
    exact Bool.noConfusion this
  · intro z
    have := (and_twoPow_eq_zero_iff x 3 (by omega)).mp (by simpa using z)
    rw [bit3] at this
    exact Bool.noConfusion this
  · constructor
    · rintro ⟨_, b⟩; exact bit4.mp b
    · intro neg; exact ⟨by omega, bit4.mpr neg⟩
  · rw [show (wordSemBytesInWord : BitVec width) = StackRemove.bytesInWord width from rfl, headVal, first]
  · rw [show (16 : BitVec width) = BitVec.ofNat width (2 ^ 4) from rfl, and_twoPow_eq_zero_iff x 4 (by omega)]
    constructor
    · intro b
      apply Classical.byContradiction
      intro neg
      have := bit4.mpr (by omega)
      rw [b] at this
      exact Bool.noConfusion this
    · intro nonneg
      cases hb : x.getLsbD 4
      · rfl
      · have := bit4.mp hb; omega
  · have : 2 ^ (width - 4) ≤ 2 ^ width := Nat.pow_le_pow_right (by decide) (by omega)
    omega

/-- HOL `memory_rel_Number_bignum_IMP`. HOL's unused existential `y` is
omitted as in `memory_rel_Number_bignum_IMP_ALT`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Number_bignum_IMP"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_number_bignumImp {width : Nat} [NeZero width]
    (c : Flapjack.Compiler.Backend.DataToWord.Config) (be : Bool) (ts : Nat)
    (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (i : Int) (v : WordLocW width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel c be ts refs sp st m dm ((.number i, v) :: vars) ∧ ¬ smallInt width i ∧ goodDimindex width →
      ∃ (w x a : BitVec width),
        v = .word w ∧ (w &&& 1) ≠ 0 ∧ getRealAddr c st w = some a ∧ dm a = true ∧ m a = .word x ∧
        (x &&& 8) ≠ 0 ∧ dm (a + wordSemBytesInWord) = true ∧
        m (a + wordSemBytesInWord) = .word (BitVec.ofNat width i.natAbs) ∧
        ((x &&& 16) = 0 ↔ 0 ≤ i) := by
  intro h
  obtain ⟨_, w, x, a, h1, h2, h3, h4, h5, h6, _, _, _, _, h7, h8, h9, _⟩ :=
    memoryRel_number_bignumImp_alt c be ts refs sp st m dm i v vars h
  exact ⟨w, x, a, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

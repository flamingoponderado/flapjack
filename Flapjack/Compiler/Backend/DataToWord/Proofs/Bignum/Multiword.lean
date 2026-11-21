module

public import Flapjack.Misc.Multiword
public import Flapjack.Compiler.Backend.DataToWord.Numbers
public import Flapjack.Misc.GoodDimindex
public import Flapjack.Misc.Multiword.Mc.Correct.Compare
public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap

@[expose] public section

/-! Multiword encodings and operation selectors in the data-to-word bignum proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Misc.Multiword Flapjack.Compiler.Backend.DataToWord

/-- A small integer whose multiword encoding is not a single digit is zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "i2mw_small_int_IMP_0"
  (words_as_type_indexed_bitvec)]
theorem i2mw_smallInt_imp_0 {width : Nat} [NeZero width] (v : Int) :
    (∀ v1 : BitVec width, i2mw v ≠ (false, [v1])) ∧ (∀ v1 : BitVec width, i2mw v ≠ (true, [v1])) ∧
      smallInt width v ∧ goodDimindex width → v = 0 := by
  rintro ⟨notF, notT, small, good⟩
  refine Classical.byContradiction fun nonzero => ?_
  have absPos : v.natAbs ≠ 0 := by omega
  have absSmall : v.natAbs < 2 ^ width := by
    rcases good with h | h <;> subst h <;> simp [smallInt] at small <;> omega
  have digits : (n2mw v.natAbs : List (BitVec width)) = [BitVec.ofNat width (v.natAbs % 2 ^ width)] := by
    rw [n2mw, if_neg absPos, Nat.div_eq_of_lt absSmall, n2mw, if_pos rfl]
  cases sign : decide (v < 0)
  · exact notF (BitVec.ofNat width (v.natAbs % 2 ^ width)) (by simp only [i2mw, sign, digits])
  · exact notT (BitVec.ofNat width (v.natAbs % 2 ^ width)) (by simp only [i2mw, sign, digits])

/-- An integer has no magnitude digits exactly when it is zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "SND_i2mw_NIL"
  (words_as_type_indexed_bitvec)]
theorem snd_i2mw_nil {width : Nat} [NeZero width] (i : Int) :
    (i2mw i : Bool × List (BitVec width)).2 = [] ↔ i = 0 := by
  simp only [i2mw]
  rw [n2mw]
  constructor
  · intro h
    split at h
    · omega
    · simp at h
  · intro h
    subst h
    simp

/-- Map an arithmetic location index to its multiword operation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "get_iop_def"]
def getIop (n : Nat) : MwOp :=
  if n = 0 then .add else
  if n = 1 then .sub else
  if n = 4 then .mul else
  if n = 5 then .div else
  .mod

/-- The header of an encoded integer is zero exactly at zero. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "mc_header_i2mw_eq_0w"
  (words_as_type_indexed_bitvec)]
theorem mcHeader_i2mw_eq_0w {width : Nat} [NeZero width] {i : Int} :
    2 * (i2mw i : Bool × List (BitVec width)).2.length + 1 < 2 ^ width →
      (mcHeader (i2mw i : Bool × List (BitVec width)) = 0 ↔ i = 0) := by
  intro h
  by_cases hi : i = 0
  · subst hi; simp [i2mw, n2mw, mcHeader]
  · simp only [hi, iff_false]
    intro e
    have hne : (i2mw i : Bool × List (BitVec width)).2 ≠ [] := by
      simp only [i2mw]
      rw [Ne, n2mw_NIL]; omega
    have hlen : 0 < (i2mw i : Bool × List (BitVec width)).2.length := List.length_pos_iff.mpr hne
    have ht := congrArg BitVec.toNat e
    rw [show i2mw i = ((i2mw i : Bool × List (BitVec width)).1,
      (i2mw i : Bool × List (BitVec width)).2) from rfl, mcHeader_toNat (by omega)] at ht
    have z : (0 : BitVec width).toNat = 0 := by simp
    rw [z] at ht; omega

/-- At a supported word width, the bignum digit count is the length of the
multiword encoding. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml"
  "bignum_digits_LENGTH_n2mw" (words_as_type_indexed_bitvec)]
theorem bignumDigits_length_n2mw {width : Nat} [NeZero width] :
    goodDimindex width →
      ∀ n : Nat, DataSem.bignumDigits (decide (width = 64)) n =
        (n2mw n : List (BitVec width)).length := by
  intro good n
  have hw : (if decide (width = 64) = true then 64 else 32) = width := by
    rcases good with h | h <;> subst h <;> decide
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [DataSem.bignumDigits, n2mw]
    by_cases h0 : n = 0
    · simp [h0]
    · have hlt : n / 2 ^ width < n :=
        Nat.div_lt_self (by omega) (Nat.one_lt_two_pow (NeZero.ne width))
      simp only [h0, if_false, hw, List.length_cons, ih _ hlt]
      omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum

module

public import Flapjack.Misc.Multiword
public import Flapjack.Compiler.Backend.DataToWord.Numbers
public import Flapjack.Misc.GoodDimindex

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

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum

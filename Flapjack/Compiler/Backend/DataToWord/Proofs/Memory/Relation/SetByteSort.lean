module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteUpdate
public import Flapjack.Misc.GoodDimindex
public import Flapjack.HolRef

@[expose] public section

/-! Reordering two byte writes at numeric lane offsets (`set_byte_sort`). -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend Flapjack.HolByte

/-- Distinct in-range numeric lane offsets select distinct byte lanes. -/
private theorem byteIndex_ofNat_ne {width : Nat} [NeZero width] (n1 n2 : Nat) (be : Bool)
    (h1 : n1 < width / 8) (h2 : n2 < width / 8) (_good : goodDimindex width) (ne : n2 ≠ n1) :
    byteIndex (BitVec.ofNat width n1) be ≠ byteIndex (BitVec.ofNat width n2) be := by
  have lt1 : n1 < 2 ^ width := lt_of_lt_of_le h1
    (le_trans (Nat.div_le_self _ _) (Nat.lt_two_pow_self).le)
  have lt2 : n2 < 2 ^ width := lt_of_lt_of_le h2
    (le_trans (Nat.div_le_self _ _) (Nat.lt_two_pow_self).le)
  simp only [byteIndex, BitVec.toNat_ofNat, Nat.mod_eq_of_lt lt1, Nat.mod_eq_of_lt lt2,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2]
  split <;> omega

open Classical in
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "set_byte_sort"
  (words_as_type_indexed_bitvec)]
theorem setByte_sort {width : Nat} [NeZero width] (b1 b2 : BitVec 8) (w : BitVec width)
    (be : Bool) :
    ∀ n1 n2 : Nat,
      setByte (BitVec.ofNat width n1) b1 (setByte (BitVec.ofNat width n2) b2 w be) be =
        if n1 = n2 then setByte (BitVec.ofNat width n1) b1 w be
        else if n1 < width / 8 ∧ n2 < width / 8 ∧ goodDimindex width ∧ n2 ≠ n1 then
          setByte (BitVec.ofNat width n2) b2 (setByte (BitVec.ofNat width n1) b1 w be) be
        else setByte (BitVec.ofNat width n1) b1 (setByte (BitVec.ofNat width n2) b2 w be) be := by
  intro n1 n2
  by_cases eq : n1 = n2
  · subst eq
    simp [setByte_overwrite]
  · rw [if_neg eq]
    split
    · rename_i h
      obtain ⟨h1, h2, good, ne⟩ := h
      exact setByte_commute _ _ _ _ _ _ (byteIndex_ofNat_ne n1 n2 be h1 h2 good ne)
    · rfl

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

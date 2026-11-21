module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.BlockStack
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.SmallNumber
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers
public import Flapjack.Misc.ListEl
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Element access and small-number constants in the memory relation

Counterparts of `memory_rel_El'`, `Smallnum_bits`, `IMP_memory_rel_Number_num3`
and `IMP_memory_rel_Number_num` in
`cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml`. `EL` is
`holEl`, `bytes_in_word` is `wordSemBytesInWord`, `x ∈ dm` for the Boolean
domain is `dm x = true`, and `&n` is `Int.ofNat n`.
-/

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- HOL `memory_rel_El'`. HOL's existential `i_w` (of an independent type
`β`) does not occur in the body; as every HOL type is inhabited it is
vacuous, so it is omitted (as for the reviewed
`memory_rel_Number_bignum_header`) and no inhabitedness instance is needed. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_El'"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem memoryRel_el' {width : Nat} [NeZero width] (c : Flapjack.Compiler.Backend.DataToWord.Config)
    (be : Bool) (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (ts' tag : Nat) (vals : List Flapjack.Compiler.Backend.DataSem.Value)
    (ptr : WordLocW width) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (index : Nat) :
    memoryRel c be ts refs sp st m dm ((.block ts' tag vals, ptr) :: vars) ∧ goodDimindex width ∧
        index < vals.length →
      ∃ ptrW x : BitVec width, ptr = .word ptrW ∧ getRealAddr c st ptrW = some x ∧
        dm (x + wordSemBytesInWord + wordSemBytesInWord * BitVec.ofNat width index) = true ∧
        memoryRel c be ts refs sp st m dm
          ((holEl index vals, m (x + wordSemBytesInWord + wordSemBytesInWord * BitVec.ofNat width index)) ::
            (.block ts' tag vals, ptr) :: vars) := by
  rintro ⟨rel, good, bound⟩
  obtain ⟨w, addr, _, locEq, real, inside, extended⟩ :=
    memoryRel_elAny c be ts refs sp st m dm ts' tag vals ptr vars index bound ⟨rel, good⟩
  refine ⟨w, addr, locEq, real, inside, ?_⟩
  rw [holEl_eq_getElem index vals bound]
  exact extended

/-- Small numbers have their two low bits clear. -/
theorem smallnum_lowBits {width : Nat} [NeZero width] (i : Int) (j : Nat) (hj : j < 2) :
    (DataToWord.smallnum i : BitVec width).getLsbD j = false := by
  have h : BitVec.ofInt width (4 * i) = BitVec.ofInt width i <<< (2 : Nat) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul, BitVec.mul_comm]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_twoPow]
  rw [smallnum_i2w, h, BitVec.getLsbD_shiftLeft]
  simp [hj]

/-- HOL `Smallnum_bits`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "Smallnum_bits"
  (words_as_type_indexed_bitvec)]
theorem smallnum_bits {wa : Nat} {wb : Nat} [NeZero wa] [NeZero wb] (i : Int) :
    (1 &&& (DataToWord.smallnum i : BitVec wa)) = 0 ∧ (2 &&& (DataToWord.smallnum i : BitVec wb)) = 0 := by
  have mask : ∀ {width : Nat}, ∀ k : Nat, k < 4 → ∀ j, ¬ j < 2 → (BitVec.ofNat width k).getLsbD j = false := by
    intro width k hk j hj
    rw [BitVec.getLsbD_ofNat]
    have : Nat.testBit k j = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hk (by
        calc 4 = 2 ^ 2 := by decide
          _ ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]
  have z0 : ∀ {width : Nat} j, (0 : BitVec width).getLsbD j = false := by simp
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j _ <;> rw [BitVec.getLsbD_and, z0]
  · by_cases small : j < 2
    · rw [smallnum_lowBits i j small, Bool.and_false]
    · rw [show (1 : BitVec wa) = BitVec.ofNat wa 1 from rfl, mask 1 (by decide) j small, Bool.false_and]
  · by_cases small : j < 2
    · rw [smallnum_lowBits i j small, Bool.and_false]
    · rw [show (2 : BitVec wb) = BitVec.ofNat wb 2 from rfl, mask 2 (by decide) j small, Bool.false_and]

/-- The `n2w n << 2` encoding of a natural number is its `Smallnum`. -/
theorem smallnum_ofNat_shift {width : Nat} [NeZero width] (n : Nat) :
    (DataToWord.smallnum (Int.ofNat n) : BitVec width) = BitVec.ofNat width n <<< (2 : Nat) := by
  rw [smallnum_i2w]
  have cast : (4 : Int) * Int.ofNat n = ((4 * n : Nat) : Int) := by push_cast; rfl
  rw [cast, BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  rw [Nat.mod_mul_mod, Nat.mul_comm]

/-- HOL `IMP_memory_rel_Number_num3`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "IMP_memory_rel_Number_num3"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem impMemoryRel_number_num3 {width : Nat} [NeZero width] (c : Flapjack.Compiler.Backend.DataToWord.Config)
    (be : Bool) (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (n : Nat) :
    goodDimindex width ∧ n < 2 ^ (width - 3) ∧ memoryRel c be ts refs sp st m dm vars →
      memoryRel c be ts refs sp st m dm
        ((.number (Int.ofNat n), .word (BitVec.ofNat width n <<< (2 : Nat))) :: vars) := by
  rintro ⟨good, bound, rel⟩
  rw [← smallnum_ofNat_shift]
  apply impMemoryRel_number c be ts refs sp st m dm vars (Int.ofNat n)
  refine ⟨good, ?_, rel⟩
  rcases good with rfl | rfl <;> simp [smallInt] at bound ⊢ <;> omega

/-- HOL `IMP_memory_rel_Number_num`. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "IMP_memory_rel_Number_num"
  (fmap_as_finite_support_relation := [st]) (words_as_type_indexed_bitvec)]
theorem impMemoryRel_number_num {width : Nat} [NeZero width] (c : Flapjack.Compiler.Backend.DataToWord.Config)
    (be : Bool) (ts : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value)) (sp : Nat)
    (st : HolFiniteMapExact WordStoreHOL (WordLocW width)) (m : BitVec width → WordLocW width)
    (dm : BitVec width → Bool) (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) (n : Nat) :
    goodDimindex width ∧ n < 2 ^ (width - 4) ∧ memoryRel c be ts refs sp st m dm vars →
      memoryRel c be ts refs sp st m dm
        ((.number (Int.ofNat n), .word (BitVec.ofNat width n <<< (2 : Nat))) :: vars) := by
  rintro ⟨good, bound, rel⟩
  apply impMemoryRel_number_num3 c be ts refs sp st m dm vars n ⟨good, ?_, rel⟩
  rcases good with rfl | rfl <;> simp at bound ⊢ <;> omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

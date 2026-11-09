module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare

@[expose] public section

/-! Arithmetic on the immediate integer representation. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- A related number with a clear pointer bit is small. This is Flapjack
infrastructure for the arithmetic proofs. -/
theorem memoryRel_numberSmallOfLowBit {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i : Int) (word : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width))
    (good : goodDimindex width)
    (inv : memoryRel conf bigEndian next refs space store memory domain ((.number i, .word word) :: vars))
    (low : word.getLsbD 0 = false) : smallInt width i := by
  obtain ⟨v, heq, hbit⟩ := memoryRel_anyNumberImp conf bigEndian next refs space store memory domain
    i (.word word) vars ⟨good, inv⟩
  have equal : word = v := WordLocW.word.inj heq
  subst v
  by_contra notSmall
  have set := hbit.mpr notSmall
  rw [low] at set
  contradiction

/-- If four times an integer fits a signed target word, that integer is small.
This is Flapjack arithmetic infrastructure. -/
theorem smallInt_of_signedQuad {width : Nat} [NeZero width] (good : goodDimindex width) (i : Int)
    (lower : - (2 : Int) ^ (width - 1) ≤ 4 * i)
    (upper : 4 * i < (2 : Int) ^ (width - 1)) : smallInt width i := by
  rcases good with h | h <;> subst width <;> norm_num [smallInt] at lower upper ⊢ <;> omega

/-- Adding two immediate integers without signed overflow preserves the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Add"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_add {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i j : Int) (wi wj : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.number i, .word wi) :: (.number j, .word wj) :: vars) ∧
      wi.getLsbD 0 = false ∧ wj.getLsbD 0 = false ∧ goodDimindex width ∧
      (wi + wj).toInt = wi.toInt + wj.toInt →
    memoryRel conf bigEndian next refs space store memory domain ((.number (i + j), .word (wi + wj)) :: vars) := by
  rintro ⟨inv, lowi, lowj, good, noOverflow⟩
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number i, .word wi) ((.number j, .word wj) :: vars) inv
  have tail2 := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number j, .word wj) vars tail
  have smalli := memoryRel_numberSmallOfLowBit conf bigEndian next refs space store memory domain i wi _ good inv lowi
  have smallj := memoryRel_numberSmallOfLowBit conf bigEndian next refs space store memory domain j wj vars good tail lowj
  have eqi := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain i (.word wi) _
    ⟨good, smalli, inv⟩)
  have eqj := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain j (.word wj) vars
    ⟨good, smallj, tail⟩)
  have boundsI := smallnum_signedBounds good i smalli
  have boundsJ := smallnum_signedBounds good j smallj
  have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have signedI : wi.toInt = 4 * i := by
    rw [eqi, smallnum_i2w, BitVec.toInt_ofInt_eq_self pos boundsI.1 boundsI.2]
  have signedJ : wj.toInt = 4 * j := by
    rw [eqj, smallnum_i2w, BitVec.toInt_ofInt_eq_self pos boundsJ.1 boundsJ.2]
  have lower := BitVec.le_toInt (wi + wj)
  have upper := BitVec.toInt_lt (x := wi + wj)
  rw [noOverflow, signedI, signedJ] at lower upper
  have smallResult : smallInt width (i + j) := smallInt_of_signedQuad good (i + j) (by omega) (by omega)
  have result := impMemoryRel_number conf bigEndian next refs space store memory domain vars (i + j)
    ⟨good, smallResult, tail2⟩
  have wordEq : smallnum (width := width) (i + j) = wi + wj := by
    rw [eqi, eqj, smallnum_i2w, smallnum_i2w, smallnum_i2w]
    simp [Int.mul_add, BitVec.ofInt_add]
  simpa only [wordEq] using result

/-- Subtracting two immediate integers without signed overflow preserves the memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Sub"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_sub {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i j : Int) (wi wj : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.number i, .word wi) :: (.number j, .word wj) :: vars) ∧
      wi.getLsbD 0 = false ∧ wj.getLsbD 0 = false ∧ goodDimindex width ∧
      (wi - wj).toInt = wi.toInt - wj.toInt →
    memoryRel conf bigEndian next refs space store memory domain ((.number (i - j), .word (wi - wj)) :: vars) := by
  rintro ⟨inv, lowi, lowj, good, noOverflow⟩
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number i, .word wi) ((.number j, .word wj) :: vars) inv
  have tail2 := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number j, .word wj) vars tail
  have smalli := memoryRel_numberSmallOfLowBit conf bigEndian next refs space store memory domain i wi _ good inv lowi
  have smallj := memoryRel_numberSmallOfLowBit conf bigEndian next refs space store memory domain j wj vars good tail lowj
  have eqi := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain i (.word wi) _
    ⟨good, smalli, inv⟩)
  have eqj := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain j (.word wj) vars
    ⟨good, smallj, tail⟩)
  have boundsI := smallnum_signedBounds good i smalli
  have boundsJ := smallnum_signedBounds good j smallj
  have pos : 0 < width := Nat.pos_of_ne_zero (NeZero.ne width)
  have signedI : wi.toInt = 4 * i := by
    rw [eqi, smallnum_i2w, BitVec.toInt_ofInt_eq_self pos boundsI.1 boundsI.2]
  have signedJ : wj.toInt = 4 * j := by
    rw [eqj, smallnum_i2w, BitVec.toInt_ofInt_eq_self pos boundsJ.1 boundsJ.2]
  have lower := BitVec.le_toInt (wi - wj)
  have upper := BitVec.toInt_lt (x := wi - wj)
  rw [noOverflow, signedI, signedJ] at lower upper
  have smallResult : smallInt width (i - j) := smallInt_of_signedQuad good (i - j) (by omega) (by omega)
  have result := impMemoryRel_number conf bigEndian next refs space store memory domain vars (i - j)
    ⟨good, smallResult, tail2⟩
  have wordEq : smallnum (width := width) (i - j) = wi - wj := by
    rw [eqi, eqj, smallnum_i2w, smallnum_i2w, smallnum_i2w]
    rw [Int.mul_sub, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]
  simpa only [wordEq] using result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

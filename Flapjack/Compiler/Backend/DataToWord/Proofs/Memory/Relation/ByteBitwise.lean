import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberArithmetic

/-! Bitwise operations on source byte-valued integers. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataSem

/-- The immediate encoding of a byte is its zero extension multiplied by four.
This is Flapjack bit-vector infrastructure. -/
theorem smallnum_byte {width : Nat} [NeZero width] (byte : BitVec 8) :
    smallnum (width := width) (Int.ofNat byte.toNat) = 4 * byte.setWidth width := by
  rw [smallnum_i2w, BitVec.ofInt_mul]
  simp

/-- Every byte value fits the immediate range at both supported widths.
This is Flapjack arithmetic infrastructure. -/
theorem smallInt_byte {width : Nat} [NeZero width] (good : goodDimindex width) (byte : BitVec 8) :
    smallInt width (Int.ofNat byte.toNat) := by
  have bound := byte.isLt
  rcases good with h | h <;> subst width <;> norm_num [smallInt] at bound ⊢ <;> omega

/-- The immediate byte encoding commutes with the source bitwise operations.
This is Flapjack bit-vector infrastructure. -/
theorem smallnum_byte_bitwise {width : Nat} [NeZero width] (good : goodDimindex width) (i j : BitVec 8) :
    (smallnum (width := width) (Int.ofNat i.toNat) &&& smallnum (Int.ofNat j.toNat) =
      smallnum (Int.ofNat (i &&& j).toNat)) ∧
    (smallnum (width := width) (Int.ofNat i.toNat) ||| smallnum (Int.ofNat j.toNat) =
      smallnum (Int.ofNat (i ||| j).toNat)) ∧
    (smallnum (width := width) (Int.ofNat i.toNat) ^^^ smallnum (Int.ofNat j.toNat) =
      smallnum (Int.ofNat (i ^^^ j).toNat)) := by
  simp only [smallnum_byte]
  rcases good with h | h <;> subst width <;> constructor
  all_goals bv_decide

/-- Bitwise and on byte-valued integers preserves the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_And"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_byteAnd {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i j : BitVec 8) (wi wj : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.number (Int.ofNat i.toNat), .word wi) :: (.number (Int.ofNat j.toNat), .word wj) :: vars) ∧
      goodDimindex width →
    memoryRel conf bigEndian next refs space store memory domain
      ((.number (Int.ofNat (i &&& j).toNat), .word (wi &&& wj)) :: vars) := by
  rintro ⟨inv, good⟩
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number (Int.ofNat i.toNat), .word wi) ((.number (Int.ofNat j.toNat), .word wj) :: vars) inv
  have tail2 := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number (Int.ofNat j.toNat), .word wj) vars tail
  have eqi := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain
    (Int.ofNat i.toNat) (.word wi) _ ⟨good, smallInt_byte good i, inv⟩)
  have eqj := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain
    (Int.ofNat j.toNat) (.word wj) vars ⟨good, smallInt_byte good j, tail⟩)
  have result := impMemoryRel_number conf bigEndian next refs space store memory domain vars
    (Int.ofNat (i &&& j).toNat) ⟨good, smallInt_byte good (i &&& j), tail2⟩
  rw [eqi, eqj, (smallnum_byte_bitwise good i j).1]
  exact result

/-- Bitwise or on byte-valued integers preserves the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Or"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_byteOr {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i j : BitVec 8) (wi wj : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.number (Int.ofNat i.toNat), .word wi) :: (.number (Int.ofNat j.toNat), .word wj) :: vars) ∧
      goodDimindex width →
    memoryRel conf bigEndian next refs space store memory domain
      ((.number (Int.ofNat (i ||| j).toNat), .word (wi ||| wj)) :: vars) := by
  rintro ⟨inv, good⟩
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number (Int.ofNat i.toNat), .word wi) ((.number (Int.ofNat j.toNat), .word wj) :: vars) inv
  have tail2 := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number (Int.ofNat j.toNat), .word wj) vars tail
  have eqi := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain
    (Int.ofNat i.toNat) (.word wi) _ ⟨good, smallInt_byte good i, inv⟩)
  have eqj := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain
    (Int.ofNat j.toNat) (.word wj) vars ⟨good, smallInt_byte good j, tail⟩)
  have result := impMemoryRel_number conf bigEndian next refs space store memory domain vars
    (Int.ofNat (i ||| j).toNat) ⟨good, smallInt_byte good (i ||| j), tail2⟩
  rw [eqi, eqj, (smallnum_byte_bitwise good i j).2.1]
  exact result

/-- Bitwise xor on byte-valued integers preserves the full memory relation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "memory_rel_Xor"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
theorem memoryRel_byteXor {width : Nat} [NeZero width] (conf : Config) (bigEndian : Bool)
    (next : Nat) (refs : Spt (BvlSem.Ref Flapjack.Compiler.Backend.DataSem.Value))
    (space : Nat) (store : HolFiniteMapExact WordStoreHOL (WordLocW width))
    (memory : BitVec width → WordLocW width) (domain : BitVec width → Bool)
    (i j : BitVec 8) (wi wj : BitVec width)
    (vars : List (Flapjack.Compiler.Backend.DataSem.Value × WordLocW width)) :
    memoryRel conf bigEndian next refs space store memory domain
      ((.number (Int.ofNat i.toNat), .word wi) :: (.number (Int.ofNat j.toNat), .word wj) :: vars) ∧
      goodDimindex width →
    memoryRel conf bigEndian next refs space store memory domain
      ((.number (Int.ofNat (i ^^^ j).toNat), .word (wi ^^^ wj)) :: vars) := by
  rintro ⟨inv, good⟩
  have tail := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number (Int.ofNat i.toNat), .word wi) ((.number (Int.ofNat j.toNat), .word wj) :: vars) inv
  have tail2 := memoryRel_tl conf bigEndian next refs space store memory domain
    (.number (Int.ofNat j.toNat), .word wj) vars tail
  have eqi := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain
    (Int.ofNat i.toNat) (.word wi) _ ⟨good, smallInt_byte good i, inv⟩)
  have eqj := WordLocW.word.inj (memoryRel_numberImp conf bigEndian next refs space store memory domain
    (Int.ofNat j.toNat) (.word wj) vars ⟨good, smallInt_byte good j, tail⟩)
  have result := impMemoryRel_number conf bigEndian next refs space store memory domain vars
    (Int.ofNat (i ^^^ j).toNat) ⟨good, smallInt_byte good (i ^^^ j), tail2⟩
  rw [eqi, eqj, (smallnum_byte_bitwise good i j).2.2]
  exact result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

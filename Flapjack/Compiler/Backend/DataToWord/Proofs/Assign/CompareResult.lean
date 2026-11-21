module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.CompareLoop
@[expose] public section

/-! Signed comparison of the three-way integer comparison result. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
set_option maxRecDepth 8192
/-- Less compares the three-way result with the integer order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_cmp_Less_word_cmp_res"
  (words_as_type_indexed_bitvec)]
theorem wordCmpLessResult {width : Nat} [NeZero width] (i j : Int) :
    goodDimindex width → (Encoders.Asm.wordCmpHOL .less (wordCmpRes i j : BitVec width) 1 = true ↔ i < j) := by
  intro good
  rcases good with h | h <;> subst width <;> by_cases eq : i = j <;> by_cases lt : i < j <;>
    norm_num [wordCmpRes, Encoders.Asm.wordCmpHOL, Encoders.Asm.holAsmSignedLess, eq, lt] <;> simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] <;> norm_num
/-- NotLess compares the three-way result with the integer order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_cmp_NotLess_word_cmp_res"
  (words_as_type_indexed_bitvec)]
theorem wordCmpNotLessResult {width : Nat} [NeZero width] (i j : Int) :
    goodDimindex width → (Encoders.Asm.wordCmpHOL .notLess 1 (wordCmpRes i j : BitVec width) = true ↔ i ≤ j) := by
  intro good
  rcases good with h | h <;> subst width <;> by_cases eq : i = j <;> by_cases lt : i < j <;>
    norm_num [wordCmpRes, Encoders.Asm.wordCmpHOL, Encoders.Asm.holAsmSignedLess, eq, lt] <;> simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] <;> norm_num <;> omega
/-- The negated NotLess comparison gives the reverse strict order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "word_cmp_not_NotLess_word_cmp_res"
  (words_as_type_indexed_bitvec)]
theorem wordCmpNotNotLessResult {width : Nat} [NeZero width] (i j : Int) :
    goodDimindex width → (Encoders.Asm.wordCmpHOL .notLess 1 (wordCmpRes i j : BitVec width) = false ↔ j < i) := by
  intro good
  have h := wordCmpNotLessResult i j good
  cases test : Encoders.Asm.wordCmpHOL .notLess 1 (wordCmpRes i j : BitVec width) <;> simp_all
/-- The negated Less comparison gives the reverse non-strict order. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "not_word_cmp_Less_word_cmp_res"
  (words_as_type_indexed_bitvec)]
theorem notWordCmpLessResult {width : Nat} [NeZero width] (i j : Int) :
    goodDimindex width → (Encoders.Asm.wordCmpHOL .less (wordCmpRes i j : BitVec width) 1 = false ↔ j ≤ i) := by
  intro good
  have h := wordCmpLessResult i j good
  cases test : Encoders.Asm.wordCmpHOL .less (wordCmpRes i j : BitVec width) 1 <;> simp_all
end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

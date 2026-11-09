import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.NumberCompare

/-! Word-level big-integer comparison used by the memory relation proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- Encode the three-way comparison of source integers as a target word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_cmp_res_def"
  (words_as_type_indexed_bitvec)]
def wordCmpRes {width : Nat} [NeZero width] (i j : Int) : BitVec width :=
  if i = j then 1 else if i < j then 0 else 2

/-- Compare two equally long arrays of target words, starting at their last
cells and moving towards lower addresses. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_cmp_loop_def"
  (words_as_type_indexed_bitvec)]
def wordCmpLoop {width : Nat} [NeZero width] (len a1 a2 : BitVec width)
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width) : Option (BitVec width) :=
  if len = 0 then some 1 else
  if domain a1 = true ∧ domain a2 = true then
    match memory a1, memory a2 with
    | .word w1, .word w2 =>
      if w1 = w2 then wordCmpLoop (len - 1) (a1 - StackRemove.bytesInWord width)
        (a2 - StackRemove.bytesInWord width) domain memory
      else if w1 < w2 then some 0 else some 2
    | _, _ => none
  else none
termination_by len.toNat
decreasing_by exact WordGcFunctions.bitVec_toNat_sub_one_lt (by assumption)

/-- A successful comparison of an array against itself returns equality. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_cmp_loop_refl"
  (words_as_type_indexed_bitvec)]
theorem wordCmpLoop_refl {width : Nat} [NeZero width] (len a : BitVec width)
    (domain : BitVec width → Bool) (memory : BitVec width → WordLocW width) (x : BitVec width)
    (result : wordCmpLoop len a a domain memory = some x) : x = 1 := by
  induction h : len.toNat using Nat.strong_induction_on generalizing len a with
  | h n ih =>
    by_cases zero : len = 0
    · simp [wordCmpLoop, zero] at result
      exact result.symm
    · rw [wordCmpLoop] at result
      simp only [zero, ↓reduceIte, and_self] at result
      by_cases inDomain : domain a = true
      · simp only [inDomain, ↓reduceIte] at result
        cases hm : memory a with
        | word w =>
          simp only [hm, ↓reduceIte] at result
          exact ih (len - 1).toNat (by rw [← h]; exact WordGcFunctions.bitVec_toNat_sub_one_lt zero)
            (len - 1) (a - StackRemove.bytesInWord width) result rfl
        | loc block offset => simp [hm] at result
      · simp [inDomain] at result

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

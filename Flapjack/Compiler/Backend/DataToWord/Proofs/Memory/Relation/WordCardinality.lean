import Flapjack.Compiler.Backend.Semantics.WordSem.Accessors
import Mathlib.Data.List.Nodup
import Mathlib.Data.Fintype.Card

/-! Cardinality of lists of concrete machine words. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack
open Classical
noncomputable section

/-- A list of distinct word locations has at most one entry per machine word. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "word_list_limit"
  (words_as_type_indexed_bitvec)]
theorem wordListLimit {width : Nat} [NeZero width] (words : List (WordLocW width)) :
    words.all wordSemIsWordLoc = true ∧ words.Nodup → words.length ≤ 2 ^ width := by
  rintro ⟨allWords, distinct⟩
  have inWords := List.all_eq_true.mp allWords
  let encode : WordLocW width → Fin (2 ^ width) := fun w => (wordSemTheWord w).toFin
  have mapped : (words.map encode).Nodup := by
    apply List.Nodup.map_on ?_ distinct
    intro x hx y hy same
    have xWord := inWords x hx
    have yWord := inWords y hy
    cases x with
    | loc label offset => simp [wordSemIsWordLoc] at xWord
    | word a =>
      cases y with
      | loc label offset => simp [wordSemIsWordLoc] at yWord
      | word b =>
        have equal : a = b := BitVec.eq_of_toFin_eq same
        subst b
        rfl
  have bound := mapped.length_le_card
  simpa using bound

end
end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

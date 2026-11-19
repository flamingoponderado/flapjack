module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.WordCondAdd
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.StoreList
public import Flapjack.Compiler.Backend.Semantics.WordSem.CallHelpers

@[expose] public section

/-! Constant-word stores in data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

/-- A successful list store has the same addresses and final memory as the
word-language constant-store operation. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "store_list_word_cond_add_IMP"
  (words_as_type_indexed_bitvec)]
theorem storeList_wordCondAdd_imp {width : Nat} [NeZero width]
    (conf : Config) (domain : BitVec width → Bool) (words : List (Bool × BitVec width))
    (memory : BitVec width → WordLocW width) (offset : BitVec width)
    (result : BitVec width → WordLocW width) (address : BitVec width)
    (run : storeList address
      (words.map (fun (flag, word) => wordCondAdd conf offset (flag, .word word))) memory domain = some result) :
    wordSemConstAddresses address words domain = true ∧
      wordSemConstWrites address (offset <<< (shiftLength conf - wordShiftAmount width)) words memory = result := by
  induction words generalizing address memory with
  | nil => simpa [storeList, wordSemConstAddresses, wordSemConstWrites] using run
  | cons entry tail ih =>
    obtain ⟨flag, word⟩ := entry
    by_cases inside : domain address = true
    · simp only [List.map_cons, storeList, inside, ↓reduceIte] at run
      obtain ⟨allInside, memoryEq⟩ := ih _ _ run
      constructor
      · simp [wordSemConstAddresses, inside, allInside]
      · cases flag <;> simpa [wordSemConstWrites, wordCondAdd] using memoryEq
    · simp [storeList, inside] at run

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

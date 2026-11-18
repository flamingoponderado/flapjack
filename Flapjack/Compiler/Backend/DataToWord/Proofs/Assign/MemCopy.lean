module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Assign.SetGlobalsPtr

@[expose] public section

/-! Memory-copy operation used in the data-to-word assignment proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack

/-- Copy word-addressed values in source order, failing if either address
of a step lies outside the memory domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "memcopy_def"
  (words_as_type_indexed_bitvec)]
def memcopy {width : Nat} [NeZero width] {α : Type} :
    Nat → BitVec width → BitVec width → (BitVec width → α) →
      (BitVec width → Bool) → Option (BitVec width → α)
  | 0, _, _, memory, _ => some memory
  | k + 1, src, dest, memory, domain =>
      if domain src && domain dest then
        memcopy k (src + wordSemBytesInWord) (dest + wordSemBytesInWord)
          (fun key => if key = dest then memory src else memory key) domain
      else none

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

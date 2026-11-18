module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.Relation.ByteStore
public import Flapjack.Compiler.Backend.DataToWord.Proofs.Memory.HeapExpand

@[expose] public section

/-! Sequential word stores used by the data-to-word memory proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack

/-- Write a list of words at consecutive word addresses, failing at the
first address outside the domain. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "store_list_def"
  (words_as_type_indexed_bitvec)]
def storeList {width : Nat} [NeZero width] : BitVec width → List (WordLocW width) →
    (BitVec width → WordLocW width) → (BitVec width → Bool) → Option (BitVec width → WordLocW width)
  | _, [], memory, _ => some memory
  | address, word :: words, memory, domain =>
      if domain address then
        storeList (address + wordSemBytesInWord) words
          (fun key => if key = address then word else memory key) domain
      else none

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

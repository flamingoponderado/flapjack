module

public import Flapjack.Compiler.Backend.DataToWord.Bytes

@[expose] public section

/-! Word-list decomposition of byte packing. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Memory
open Flapjack Flapjack.Compiler.Backend.DataToWord

/-- Packing into appended word lists advances the byte input by the capacity of the first list. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_memoryProofScript.sml" "write_bytes_APPEND"
  (words_as_type_indexed_bitvec)]
theorem writeBytes_append {width : Nat} [NeZero width] (xs ys : List (BitVec width))
    (vals : List (BitVec 8)) (be : Bool) :
    writeBytes vals (xs ++ ys) be =
      writeBytes vals xs be ++ writeBytes (vals.drop ((width / 8) * xs.length)) ys be := by
  induction xs generalizing vals with
  | nil => simp [writeBytes]
  | cons head tail ih =>
    simp only [List.cons_append, writeBytes, List.length_cons]
    rw [ih]
    congr 2
    simp [Nat.mul_add, Nat.add_comm]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Memory

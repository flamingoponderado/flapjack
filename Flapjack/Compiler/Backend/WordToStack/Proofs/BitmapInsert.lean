import Flapjack.Compiler.Backend.WordToStack
import Flapjack.Compiler.Backend.Semantics.StackSem.WordBitmap
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack
open Flapjack

/-- Full original insertion decoding preservation, including the original
word-sized index bound, successful bitmap guard, prefix/counter relation, and
complete insertion-output equation. Arbitrary AppList trees and prefixes are
retained. The successful-decoding guard is retained though, as in the original
proof, the insertion/drop equality does not need it; the output is derived from the reviewed native insertion operation. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_insert_bitmap"
  (words_as_type_indexed_bitvec)]
theorem readBitmapInsertBitmap {width : Nat} [NeZero width]
    (bitmap : List (BitVec width)) (old : AppList (BitVec width)) (n : Nat)
    (new : AppList (BitVec width)) (n' index : Nat) (cur : List (BitVec width))
    (hindex : index < 2 ^ width)
    (_hbitmap : (Flapjack.StackSem.readBitmap bitmap).isSome = true)
    (hcounter : n = cur.length + (appListAppend old).length)
    (hinsert : insertBitmap bitmap (old, n) = ((new, n'), index)) :
    Flapjack.StackSem.readBitmap
      ((cur ++ appListAppend new).drop (index % 2 ^ width)) =
      Flapjack.StackSem.readBitmap bitmap := by
  simp only [insertBitmap, Prod.mk.injEq] at hinsert
  rcases hinsert with ⟨⟨htree, _hnext⟩, hoffset⟩
  rw [← htree, (appListAppend_thm old (.list bitmap) bitmap).1,
    (appListAppend_thm old (.list bitmap) bitmap).2.1]
  rw [Nat.mod_eq_of_lt hindex, ← hoffset, hcounter, ← List.append_assoc,
    ← List.length_append, List.drop_append_length]

end Flapjack.Compiler.Backend.WordToStack

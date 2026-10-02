import Flapjack.Compiler.Backend.WordToStack.Proofs.BitmapDecode
import Flapjack.Compiler.Backend.WordToStack.LiveBitmap

namespace Flapjack.Compiler.Backend.WordToStack
open Flapjack

/-- Full original write-bitmap decoding result for arbitrary Spt payloads,
register keys and frame arithmetic, including truncating natural subtraction.
Only the original dimension-at-least-eight premise is retained. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "read_bitmap_write_bitmap"
  (words_as_type_indexed_bitvec)]
theorem readBitmapWriteBitmap {width : Nat} [NeZero width] {α : Type}
    (names : Spt α) (k frame : Nat) (hwidth : 8 ≤ width) :
    Flapjack.StackSem.readBitmap (writeBitmapExact names k frame : List (BitVec width)) =
      some ((List.range frame).map (fun x => decide
        (x ∈ (sptToAList names).map (fun (r, _) => frame - 1 - (r / 2 - k))))) := by
  unfold writeBitmapExact
  simpa using readBitmapWordList (width := width)
    ((List.range frame).map (fun x => decide
      (x ∈ (sptToAList names).map (fun (r, _) => frame - 1 - (r / 2 - k))))) [] hwidth

end Flapjack.Compiler.Backend.WordToStack

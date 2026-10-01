import Flapjack.Compiler.Backend.WordToStack

namespace Flapjack.Compiler.Backend.WordToStack
open Flapjack

/-- The source insertion-prefix theorem is payload-polymorphic, just like the
reviewed insertion definition; no word dimension or bitmap-count bound occurs. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "insert_bitmap_isPREFIX"]
theorem insertBitmapIsPrefix {α : Type} (words : List α)
    (bitmaps output : AppList α × Nat) (index : Nat)
    (h : insertBitmap words bitmaps = (output, index)) :
    (appListAppend bitmaps.1).IsPrefix (appListAppend output.1) := by
  have hout := congrArg Prod.fst h
  simp only [insertBitmap] at hout
  rw [← hout, (appListAppend_thm bitmaps.1 (.list words) words).1]
  exact ⟨words, by simp [appListAppend, appendAux]⟩

end Flapjack.Compiler.Backend.WordToStack

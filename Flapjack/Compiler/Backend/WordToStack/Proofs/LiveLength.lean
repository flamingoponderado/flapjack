import Flapjack.Compiler.Backend.WordToStack.NativeLive

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- The original bitmap accounting result over the actual native frame insertion.
The full output equation and input bound are retained; cutsets and frames are
arbitrary. Only HOL's type-indexed positive word dimension is translated. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wLive_LENGTH"
  (words_as_type_indexed_bitvec)]
theorem wLiveLength {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bitmaps : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (program : HolProg width)
    (output : AppList (BitVec width) × Nat)
    (h : wLiveNative live bitmaps frame = (program, output) ∧
      (appListAppend bitmaps.1).length ≤ bitmaps.2) :
    (appListAppend output.1).length ≤ output.2 ∧
      bitmaps.2 - (appListAppend bitmaps.1).length =
        output.2 - (appListAppend output.1).length := by
  have hout := congrArg Prod.snd h.1
  by_cases empty : frame.2.1 = 0
  · simp only [wLiveNative, empty, ↓reduceIte] at hout
    subst output
    exact ⟨h.2, rfl⟩
  · simp only [wLiveNative, empty, ↓reduceIte, insertBitmap] at hout
    rw [← hout]
    rw [(appListAppend_thm bitmaps.1
      (.list (writeBitmapExact live.2 frame.1 frame.2.2))
      (writeBitmapExact live.2 frame.1 frame.2.2)).1]
    simp only [appListAppend, appendAux, List.append_nil, List.length_append]
    constructor
    · exact Nat.add_le_add_right h.2 _
    · omega

end Flapjack.Compiler.Backend.WordToStack.Native

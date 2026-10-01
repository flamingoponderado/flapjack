import Flapjack.Compiler.Backend.WordToStack.NativeLive

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang

/-- Full source frame-insertion prefix result. Cutsets, frame and bitmap tree
are arbitrary; no input length bound or wellformedness premise is added. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "wLive_isPREFIX"
  (words_as_type_indexed_bitvec)]
theorem wLiveIsPrefix {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bitmaps : AppList (BitVec width) × Nat)
    (frame : Nat × Nat × Nat) (program : HolProg width)
    (output : AppList (BitVec width) × Nat)
    (h : wLiveNative live bitmaps frame = (program, output)) :
    (appListAppend bitmaps.1).IsPrefix (appListAppend output.1) := by
  have hout := congrArg Prod.snd h
  by_cases empty : frame.2.1 = 0
  · simp only [wLiveNative, empty, ↓reduceIte] at hout
    subst output
    exact ⟨[], by simp⟩
  · simp only [wLiveNative, empty, ↓reduceIte, insertBitmap] at hout
    rw [← hout]
    rw [(appListAppend_thm bitmaps.1
      (.list (writeBitmapExact live.2 frame.1 frame.2.2))
      (writeBitmapExact live.2 frame.1 frame.2.2)).1]
    exact ⟨_, rfl⟩

end Flapjack.Compiler.Backend.WordToStack.Native

import Flapjack.Compiler.Backend.WordToStack.ProductionBitmapWrite

/-! Fresh original wLive outcomes captured in word_to_stack_bitmap_index_probe.out.
These kernel regressions cover whole program/state pairs, and separately the
actual repaired production writer/consumer. They are not equivalence proofs. -/
namespace Flapjack.Test.WordToStackBitmapIndexParity
open Flapjack Compiler.Backend.WordToStack Compiler.Backend.WordToStack.Native
open Compiler.Backend.StackLang

-- index_width1_wrap: original 2w at word1 is zero; data length is independent
-- of the retained stored count, exactly as in the original input pair.
example : wLiveNative (width := 1) (.ln, .ln) (.list [4], 1) (22, 2, 1) =
    (.seq (.inst (.const 22 0)) (.stackStore 22 0),
      .append (.list [4]) (.list [0]), 2) := by
  simp [wLiveNative, insertBitmap, writeBitmapExact, sptToAList, sptFoldi,
    wordListW]
  decide +kernel

-- index_width8_wrap
example : wLiveNative (width := 8) (.ln, .ln) (.list [4], 255) (22, 2, 1) =
    (.seq (.inst (.const 22 0)) (.stackStore 22 0),
      .append (.list [4]) (.list [2]), 256) := by
  simp [wLiveNative, insertBitmap, writeBitmapExact, sptToAList, sptFoldi,
    wordListW]
  decide +kernel

-- index_width8_below
example : wLiveNative (width := 8) (.ln, .ln) (.list [4], 254) (22, 2, 1) =
    (.seq (.inst (.const 22 255)) (.stackStore 22 0),
      .append (.list [4]) (.list [2]), 255) := by
  simp [wLiveNative, insertBitmap, writeBitmapExact, sptToAList, sptFoldi,
    wordListW]
  decide +kernel

-- index_empty_frame
example : wLiveNative (width := 8) (.ln, .ln) (.list [4], 255) (22, 0, 1) =
    (.skip, .list [4], 255) := by
  rfl

/-- Concrete executed writer at the word8 wrap boundary, including bitmap
contents and count. Generic macro conversion would have rejected this index. -/
example :
    let actual := RiscV.wordStackBitmapWriteWithBuilder
      ({ locations := [], scratch := 22, stackBase := 0 } : RiscV.WordStackConfig)
      22 1 { data := [4], length := 255 } [] (fun _ => [2])
    (Compiler.Backend.StackToLab.Production.toNative? (width := 8) actual.1,
      actual.2) =
      (some (.seq (.inst (.const 22 0)) (.stackStore 22 0)),
        { data := [4, 2], length := 256 }) := by
  dsimp only
  rw [ProductionBitmapWrite.writerConsumer]
  simp [RiscV.wordStackBitmapWriteWithBuilder, RiscV.wordStackInsertBitmap,
    RiscV.wordStackOffset]

end Flapjack.Test.WordToStackBitmapIndexParity

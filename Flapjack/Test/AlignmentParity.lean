import Flapjack.Misc.Alignment

namespace Flapjack.Test.AlignmentParity
open Flapjack

/-! Kernel replay of `scripts/hol-probes/alignment_align_probe.out`: original HOL `word_slice`,
`align` and `aligned` EVAL results, and the 64-bit `byte_align`/`byte_aligned` facts HOL proves
through `LOG2 8 = 3`, proved here through the same `LOG_UNIQUE` step. -/

private theorem log2_8 : holLOG2 8 = 3 := holLOG_UNIQUE 2 8 3 ⟨by decide, by decide⟩

-- al_align_type=:num -> α word -> α word
example : Nat → BitVec 64 → BitVec 64 := holAlign
-- al_byte_align_type=:α word -> α word
noncomputable example : BitVec 64 → BitVec 64 := holByteAlign
-- al_slice_7_4=192w
example : holWordSlice 7 4 (0xABCD : BitVec 16) = 192 := by decide +kernel
-- al_slice_20_4=43968w
example : holWordSlice 20 4 (0xABCD : BitVec 16) = 43968 := by decide +kernel
-- al_slice_3_9=0w
example : holWordSlice 3 9 (0xABCD : BitVec 16) = 0 := by decide +kernel
-- al_align_3=0x12340w
example : holAlign 3 (0x12345 : BitVec 32) = 0x12340 := by decide +kernel
-- al_align_0=0x12345w
example : holAlign 0 (0x12345 : BitVec 32) = 0x12345 := by decide +kernel
-- al_align_40=0w
example : holAlign 40 (0x12345 : BitVec 32) = 0 := by decide +kernel
-- al_aligned_t=T
example : holAligned 2 (12 : BitVec 8) = true := by decide +kernel
-- al_aligned_f=F
example : holAligned 2 (13 : BitVec 8) = false := by decide +kernel
-- al_byte_align_64=byte_align 0x1234567w = 0x1234560w
example : holByteAlign (0x1234567 : BitVec 64) = 0x1234560 := by
  show holAlign (holLOG2 (64 / 8)) _ = _
  rw [show (64 : Nat) / 8 = 8 from rfl, log2_8]; decide +kernel
-- al_byte_aligned_64=byte_aligned 16w
example : holByteAligned (16 : BitVec 64) = true := by
  show holAligned (holLOG2 (64 / 8)) _ = _
  rw [show (64 : Nat) / 8 = 8 from rfl, log2_8]; decide +kernel

end Flapjack.Test.AlignmentParity

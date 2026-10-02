import Flapjack.Compiler.Backend.LabToTarget.WordLocValByte

namespace Flapjack.Test.LabToTargetWordLocValByteParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget

private def labs : Spt (Spt Nat) := sptInsert 7 (sptInsert 3 291 .ln) .ln

-- Literal original word32 observations: little/big endian and real label lookup.
example : wordLocValByte (0 : BitVec 32) .ln (fun _ => .word 0x44332211) 1 false =
    some 34 := by
  change some (HolByte.getByte (1 : BitVec 32) 0x44332211 false) = some 34
  decide +kernel
example : wordLocValByte (0 : BitVec 32) .ln (fun _ => .word 0x44332211) 1 true =
    some 51 := by
  change some (HolByte.getByte (1 : BitVec 32) 0x44332211 true) = some 51
  decide +kernel
example : wordLocValByte (256 : BitVec 32) labs (fun _ => .loc 7 3) 0 false =
    some 35 := by
  rw [wordLocValByte_loc_hit (k1 := 7) (k2 := 3) (q := 291) _ _ _ _ _ rfl (by decide +kernel)]
  decide +kernel
example : wordLocValByte (0 : BitVec 32) .ln (fun _ => .loc 7 3) 0 false = none := by
  change (match wordLocVal (0 : BitVec 32) .ln (.loc 7 3) with
    | some w => some (HolByte.getByte (0 : BitVec 32) w false)
    | none => none) = none
  decide +kernel
example : wordLocValByte (0 : BitVec 32) (sptInsert 7 .ln .ln)
    (fun _ => .loc 7 3) 0 false = none := by
  exact wordLocValByte_loc_miss _ _ _ _ _ 7 3 rfl (by decide +kernel)

-- These narrow-width fixtures do not interpret LOG2(0): the memory is constant.
example : wordLocValByte (0 : BitVec 1) .ln (fun _ => .word 1) 1 false = some 0 := by
  change some (HolByte.getByte (1 : BitVec 1) 1 false) = some 0
  decide +kernel
example : wordLocValByte (0 : BitVec 1) .ln (fun _ => .word 1) 1 true = some 1 := by
  change some (HolByte.getByte (1 : BitVec 1) 1 true) = some 1
  decide +kernel

-- Actual nonconstant memory proves the address is aligned before being read.
example : wordLocValByte (0 : BitVec 32) .ln
    (fun a => if a = 0 then .word 0x44332211 else .loc 7 3) 1 false = some 34 := by
  have hlog : holLOG2 (32 / 8) = 2 := by
    rw [holLOG2_eq_log2 (by decide)]
    decide +kernel
  have ha : holByteAlign (1 : BitVec 32) = 0 := by
    unfold holByteAlign
    rw [hlog, holAlign_eq_shift]
    decide +kernel
  simp only [wordLocValByte, ha, ite_true, wordLocVal]
  decide +kernel

-- At width1, actual address-dependent memory keeps the shared symbolic LOG2(0).
example : wordLocValByte (0 : BitVec 1) .ln (fun a => .word a) 1 true =
    some ((holAlign (holLOG2 0) (1 : BitVec 1)).setWidth 8) := by
  rw [wordLocValByte_oneBit_symbolic]
  simp [wordLocVal, HolByte.getByte, HolByte.byteIndex]

end Flapjack.Test.LabToTargetWordLocValByteParity

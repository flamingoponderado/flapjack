import Flapjack.RiscV.PanMemory

/-! # `RiscV.panRiscVByteAlign` versus HOL `byte$byte_align`

HOL `byte_align_def` is `align (LOG2 (dimindex DIV 8))`, i.e. clear the low
`LOG2 (width / 8)` bits. The production `RiscV.panRiscVByteAlign` rounds down
to a multiple of `2 ^ LOG2 bytesInWord`, which is the same alignment when
`bytesInWord = width / 8`.  The checks below pin it against the direct HOL
oracle `scripts/hol-probes/byte_align_probe.out` (`ba24_5 = 4`, `ba64_13 = 8`,
`ba8_7 = 7`), including the non-power-of-two width 24 row, where an earlier
division-by-`bytesInWord` alignment returned 3. -/

namespace Flapjack.Test.PanRiscVByteAlignParity

open Flapjack RiscV

/-- Width 24, `bytesInWord = 3`: HOL aligns `5` to `4` (oracle `ba24_5 = 4w`),
    and so does production. -/
theorem width24_agrees :
    panRiscVByteAlign (BitVec.ofNat 24 3) (BitVec.ofNat 24 5) = BitVec.ofNat 24 4 ∧
      BitVec.ofNat 24 ((5 >>> 1) <<< 1) = (BitVec.ofNat 24 4) := by
  constructor <;> decide

/-- Production `Word 64` alignment is the HOL bit mask (direct oracle `ba64_13 = 8w`). -/
theorem width64_agrees :
    panRiscVByteAlign (8 : Word 64) (BitVec.ofNat 64 13) = BitVec.ofNat 64 8 := by
  decide

/-- Width 8, `bytesInWord = 1`: alignment is the identity (oracle `ba8_7 = 7w`). -/
theorem width8_agrees :
    panRiscVByteAlign (BitVec.ofNat 8 1) (BitVec.ofNat 8 7) = BitVec.ofNat 8 7 := by
  decide

/-- The general power-of-two characterization at the production width. -/
theorem width64_bitMask (address : Word 64) :
    panRiscVByteAlign (8 : Word 64) address =
      BitVec.ofNat 64 ((address.toNat >>> 3) <<< 3) :=
  panRiscVByteAlign_eight_eq_bitMask address

example : panRiscVByteAlign (BitVec.ofNat 24 3) (BitVec.ofNat 24 5) = BitVec.ofNat 24 4 :=
  width24_agrees.1

def byteAlignGuard : Bool :=
  (panRiscVByteAlign (BitVec.ofNat 24 3) (BitVec.ofNat 24 5) == BitVec.ofNat 24 4) &&
    (BitVec.ofNat 24 ((5 >>> 1) <<< 1) == (BitVec.ofNat 24 4)) &&
    (panRiscVByteAlign (8 : Word 64) (BitVec.ofNat 64 13) == BitVec.ofNat 64 8) &&
    (panRiscVByteAlign (BitVec.ofNat 8 1) (BitVec.ofNat 8 7) == BitVec.ofNat 8 7)

#eval byteAlignGuard
#guard byteAlignGuard

def runChecks : IO Bool := do
  if byteAlignGuard then
    IO.println "PASS RiscV panRiscVByteAlign vs HOL byte_align (width 24/64/8 agreement)"
    pure true
  else
    IO.println "FAIL RiscV panRiscVByteAlign vs HOL byte_align"
    pure false

end Flapjack.Test.PanRiscVByteAlignParity

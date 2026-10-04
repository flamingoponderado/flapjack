import Flapjack.Compiler.Backend.WordToStack.NativeInstructions
import Flapjack.Compiler.Backend.WordToStack.LiveBitmap

namespace Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm

/-- Literal native frame bitmap insertion. Both cutsets and the full frame
triple are retained; the source uses only the second cutset and tests f. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
def wLiveNative {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bitmaps : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) : HolProg width × (AppList (BitVec width) × Nat) :=
  if kf.2.1 = 0 then (.skip, bitmaps)
  else
    let inserted := insertBitmap (writeBitmapExact live.2 kf.1 kf.2.2) bitmaps
    (.seq (.inst (.const kf.1 (BitVec.ofNat width (inserted.2 + 1))))
      (.stackStore kf.1 0), inserted.1)

/-- Flapjack-only universal pair transport: no bitmap-domain, frame-validity
or evaluation premise, and the returned bitmap component is preserved. -/
theorem toGeneric_wLiveNative {width : Nat} [NeZero width]
    (live : Spt Unit × Spt Unit) (bitmaps : AppList (BitVec width) × Nat)
    (kf : Nat × Nat × Nat) :
    (toGeneric (wLiveNative live bitmaps kf).1, (wLiveNative live bitmaps kf).2) =
      wLiveExact live bitmaps kf := by
  by_cases empty : kf.2.1 = 0 <;>
    simp [wLiveNative, wLiveExact, empty, toGeneric, Prog.map, HolInst.toWordLangInst]

end Flapjack.Compiler.Backend.WordToStack.Native

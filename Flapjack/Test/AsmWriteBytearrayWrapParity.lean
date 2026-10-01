import Flapjack.Misc.AsmWriteBytearray

/-!
Kernel-checked wrap cases for `Flapjack.asmWriteBytearrayHOL`
(HOL `misc$asm_write_bytearray_def`, `cakeml/misc/miscScript.sml:3758-3760`).

HOL computes the tail first and then overwrites the head address:
`asm_write_bytearray a (x :: xs) m = (a =+ x) (asm_write_bytearray (a + 1w) xs m)`.
On a narrow word the successor address can wrap back onto the head address, so
the EARLIER (head) byte wins there.  With `width = 1`, address `0` and bytes
`[1, 2, 3]`, the written addresses run `0, 1, 0`; the first byte `1` must
survive at address `0`, while address `1` keeps the second byte `2`.

Paired original-HOL output: `scripts/hol-probes/misc_asm_write_bytearray_probe.out`
(rows `wa_wrap0=1w`, `wa_wrap1=2w`).
-/

namespace Flapjack.Test.AsmWriteBytearrayWrapParity

open Flapjack

/-- The first byte of the list survives at address `0` on a wrapping `width = 1`
    word, because the head update runs after the tail recursion. -/
example : asmWriteBytearrayHOL (width := 1) 0 [1, 2, 3] (fun _ => (0 : BitVec 8)) 0 = 1 := by
  decide

/-- Address `1` keeps the second byte `2` (written before the third byte wraps
    back onto address `0`). -/
example : asmWriteBytearrayHOL (width := 1) 0 [1, 2, 3] (fun _ => (0 : BitVec 8)) 1 = 2 := by
  decide

private def wrapGuard : Bool :=
  decide (asmWriteBytearrayHOL (width := 1) 0 [1, 2, 3] (fun _ => (0 : BitVec 8)) 0 = 1) &&
    decide (asmWriteBytearrayHOL (width := 1) 0 [1, 2, 3] (fun _ => (0 : BitVec 8)) 1 = 2)

#guard wrapGuard

end Flapjack.Test.AsmWriteBytearrayWrapParity

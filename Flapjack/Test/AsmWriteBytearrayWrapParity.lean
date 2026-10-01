import Flapjack.Misc.AsmWriteBytearray

/-!
Kernel-checked wrap case for `Flapjack.asmWriteBytearrayHOL`
(HOL `misc$asm_write_bytearray_def`, `cakeml/misc/miscScript.sml:3758-3760`).

HOL computes the tail first and then overwrites the head address:
`asm_write_bytearray a (x :: xs) m = (a =+ x) (asm_write_bytearray (a + 1w) xs m)`.
On a narrow word the successor address can wrap back onto the head address, so
the EARLIER (head) byte wins there.  With `width = 1`, address `0` and bytes
`[1, 2, 3]`, every written address is `0`, and the first byte `1` must survive.
-/

namespace Flapjack.Test.AsmWriteBytearrayWrapParity

open Flapjack

/-- The first byte of the list survives at address `0` on a wrapping `width = 1`
    word, because the head update runs after the tail recursion. -/
example : asmWriteBytearrayHOL (width := 1) 0 [1, 2, 3] (fun _ => (0 : BitVec 8)) 0 = 1 := by
  decide

private def wrapGuard : Bool :=
  decide (asmWriteBytearrayHOL (width := 1) 0 [1, 2, 3] (fun _ => (0 : BitVec 8)) 0 = 1)

#guard wrapGuard

end Flapjack.Test.AsmWriteBytearrayWrapParity

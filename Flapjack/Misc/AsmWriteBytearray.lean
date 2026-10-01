import Flapjack.HolRef

/-!
Exact port of HOL `misc$asm_write_bytearray_def`
(`cakeml/misc/miscScript.sml:3758-3760`), used by the target semantics
`post_ffi_asm` successor state to write the bytes returned by the FFI call.

`asm_write_bytearray a [] m = m` and
`asm_write_bytearray a (x::xs) m = (a =+ x) (asm_write_bytearray (a+1w) xs m)`.

The recursion writes the tail first and then overwrites the head address, so a
later (larger-address) byte may overwrite an earlier one when the address wraps
around; the Lean renderer keeps that head-update-after-tail-recursion order.

`'a word` is rendered as `BitVec width` with the reviewed `[NeZero width]`
discharge; `word8` is `BitVec 8`.
-/

namespace Flapjack

/-- Exact HOL `asm_write_bytearray_def` (`cakeml/misc/miscScript.sml:3758-3760`):
    `asm_write_bytearray a [] m = m` and
    `asm_write_bytearray a (x::xs) m = (a =+ x) (asm_write_bytearray (a+1w) xs m)`. -/
@[hol "cakeml/misc/miscScript.sml" "asm_write_bytearray_def" (words_as_type_indexed_bitvec)]
def asmWriteBytearrayHOL {width : Nat} [NeZero width] (address : BitVec width)
    (bytes : List (BitVec 8)) (memory : BitVec width → BitVec 8) : BitVec width → BitVec 8 :=
  match bytes with
  | [] => memory
  | x :: xs => fun k => if k = address then x else asmWriteBytearrayHOL (address + 1) xs memory k

end Flapjack

import Flapjack.HolRef

/-!
Exact port of HOL `misc$bytes_in_memory_def`
(`cakeml/misc/miscScript.sml:4176-4180`), used by the targetSem machine
prerequisites (`encoded_bytes_in_mem`, `is_valid_mapped_read/write`).

The recursive clause is `bytes_in_memory a ((x:word8)::xs) m dm <=>
(m a = x) /\ a IN dm /\ bytes_in_memory (a + 1w) xs m dm`, so the Lean
renderer checks the byte value and domain membership at `a` and recurses
at `a + 1`.
-/

namespace Flapjack

/-- Exact HOL `bytes_in_memory_def`: a byte list sits in memory from `address`
    within the domain `domain`. -/
@[hol "cakeml/misc/miscScript.sml" "bytes_in_memory_def" (words_as_type_indexed_bitvec)]
def bytesInMemoryHOL {width : Nat} [NeZero width] (address : BitVec width)
    (bytes : List (BitVec 8)) (memory : BitVec width → BitVec 8)
    (domain : BitVec width → Prop) : Prop :=
  match bytes with
  | [] => True
  | x :: xs => memory address = x ∧ domain address ∧
      bytesInMemoryHOL (address + 1) xs memory domain

end Flapjack

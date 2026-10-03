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

/-- Wrapped address reassociation; Flapjack word arithmetic infrastructure. -/
private theorem advance {width : Nat} (a : BitVec width) (n : Nat) :
    (a + 1) + BitVec.ofNat width n = a + BitVec.ofNat width (n + 1) := by
  rw [BitVec.ofNat_add, BitVec.add_assoc]
  exact congrArg (a + ·) (BitVec.add_comm _ _)
/-- Concatenation splits at the wrapped address after the prefix. -/
@[hol "cakeml/misc/miscScript.sml" "bytes_in_memory_APPEND" (words_as_type_indexed_bitvec)]
theorem bytesInMemory_append {width : Nat} [NeZero width]
    (l1 l2 : List (BitVec 8)) (pc : BitVec width)
    (mem : BitVec width → BitVec 8) (dm : BitVec width → Prop) :
    bytesInMemoryHOL pc (l1 ++ l2) mem dm ↔
      bytesInMemoryHOL pc l1 mem dm ∧
      bytesInMemoryHOL (pc + BitVec.ofNat width l1.length) l2 mem dm := by
  induction l1 generalizing pc with
  | nil => simp [bytesInMemoryHOL]
  | cons x xs ih =>
    simp only [List.cons_append, bytesInMemoryHOL, List.length_cons]
    rw [ih, advance]
    simp only [and_assoc]
/-- Memory agreement on every byte offset preserves the full byte region. -/
@[hol "cakeml/misc/miscScript.sml" "bytes_in_memory_change_mem" (words_as_type_indexed_bitvec)]
theorem bytesInMemory_changeMem {width : Nat} [NeZero width]
    (a : BitVec width) (bs : List (BitVec 8))
    (m1 m2 : BitVec width → BitVec 8) (md : BitVec width → Prop)
    (h : bytesInMemoryHOL a bs m1 md ∧
      ∀ n, n < bs.length → m1 (a + BitVec.ofNat width n) = m2 (a + BitVec.ofNat width n)) :
    bytesInMemoryHOL a bs m2 md := by
  induction bs generalizing a with
  | nil => trivial
  | cons x xs ih =>
    rcases h with ⟨⟨hx, hd, ht⟩, hm⟩
    have hz := hm 0 (by simp)
    simp at hz
    refine ⟨hz.symm.trans hx, hd, ih (a + 1) ⟨ht, ?_⟩⟩
    intro n hn
    rw [advance]
    exact hm (n + 1) (by simpa using Nat.succ_lt_succ hn)

end Flapjack

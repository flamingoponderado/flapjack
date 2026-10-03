import Flapjack.Misc.BytesInMemory

namespace Flapjack

/-- Full original domain consequence for any in-range byte index, including
wrapped addresses and byte regions longer than the address space. The only
premises are the original byte-memory predicate and index bound. -/
@[hol "cakeml/misc/miscScript.sml" "bytes_in_memory_in_domain"
  (words_as_type_indexed_bitvec)]
theorem bytesInMemoryInDomain {width : Nat} [NeZero width]
    (address : BitVec width) (bytes : List (BitVec 8))
    (memory : BitVec width → BitVec 8) (domain : BitVec width → Prop) (index : Nat)
    (hypothesis : bytesInMemoryHOL address bytes memory domain ∧ index < bytes.length) :
    domain (address + BitVec.ofNat width index) := by
  induction bytes generalizing address index with
  | nil => simp at hypothesis
  | cons head tail ih =>
    rcases hypothesis with ⟨⟨_value, inDomain, rest⟩, below⟩
    cases index with
    | zero => simpa using inDomain
    | succ index =>
      have tailBelow : index < tail.length := Nat.lt_of_succ_lt_succ below
      have result := ih (address + 1) index ⟨rest, tailBelow⟩
      have shifted : (address + 1) + BitVec.ofNat width index =
          address + BitVec.ofNat width (index + 1) := by
        rw [BitVec.ofNat_add, BitVec.add_assoc]
        exact congrArg (address + ·) (BitVec.add_comm _ _)
      rw [shifted] at result
      exact result

end Flapjack

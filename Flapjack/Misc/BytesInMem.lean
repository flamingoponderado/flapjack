import Flapjack.HolRef

namespace Flapjack

/-- Original excluded-domain memory relation. The original HOL constant type
is α word → β list → (α word → β) → (α word → bool) →
(α word → bool) → bool, confirmed by bytes_in_mem_type.sml against miscTheory.
Value polymorphism is retained; only word dimensions use positive BitVecs. -/
@[hol "cakeml/misc/miscScript.sml" "bytes_in_mem_def"
  (words_as_type_indexed_bitvec)]
def bytesInMemHOL {width : Nat} [NeZero width] {Value : Type}
    (address : BitVec width) (values : List Value)
    (memory : BitVec width → Value) (domain excluded : BitVec width → Prop) : Prop :=
  match values with
  | [] => True
  | value :: rest => domain address ∧ ¬excluded address ∧ memory address = value ∧
      bytesInMemHOL (address + 1) rest memory domain excluded

end Flapjack

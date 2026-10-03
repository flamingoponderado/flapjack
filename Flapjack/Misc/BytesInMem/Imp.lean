import Flapjack.Misc.BytesInMem
import Flapjack.Misc.BytesInMemory
namespace Flapjack

/-- Full original excluded-domain memory implication.
The original theorem fixes values to word8, though bytesInMem itself is generic.
The domain and excluded sets are arbitrary, and wrapped addresses are retained. -/
@[hol "cakeml/misc/miscScript.sml" "bytes_in_mem_IMP"
  (words_as_type_indexed_bitvec)]
theorem bytesInMem_impliesMemory {width : Nat} [NeZero width]
    (values : List (BitVec 8)) (address : BitVec width)
    (memory : BitVec width → BitVec 8) (domain excluded : BitVec width → Prop) :
    bytesInMemHOL address values memory domain excluded →
      bytesInMemoryHOL address values memory domain := by
  induction values generalizing address with
  | nil => intro _; trivial
  | cons value rest ih =>
    rintro ⟨hd,_hx,hm,ht⟩
    exact ⟨hm,hd,ih (address+1) ht⟩
end Flapjack

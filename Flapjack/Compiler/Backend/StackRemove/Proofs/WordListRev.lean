import Flapjack.Compiler.Backend.StackRemove
import Flapjack.Misc.SetSep

/-! Reverse heap-list predicate from stack_removeProofScript.sml.
The word dimension indexes addresses only. Payloads retain their independent
HOL type; each address subtraction is modular at that dimension.
-/

namespace Flapjack.Compiler.Backend.StackRemove

/-- Full reversed heap-list assertion. Both the singleton and recursive tail
use the already-subtracted address, with the exact separation conjunction. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_list_rev_def"
  (words_as_type_indexed_bitvec)]
def wordListRev {width : Nat} [NeZero width] {β : Type} (address : BitVec width) :
    List β → ((BitVec width × β) → Prop) → Prop
  | [] => Flapjack.SetSep.emp
  | value :: values =>
      Flapjack.SetSep.star
        (Flapjack.SetSep.one (address - bytesInWord width, value))
        (wordListRev (address - bytesInWord width) values)

end Flapjack.Compiler.Backend.StackRemove

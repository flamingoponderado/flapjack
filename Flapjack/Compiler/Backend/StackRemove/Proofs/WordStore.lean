import Flapjack.Compiler.Backend.StackRemove.Proofs.WordListRev
import Flapjack.Compiler.Backend.Semantics.StackSem.RegisterTransfers

/-! Full StackRemove store heap assertion, on the actual StackSem store map.
Address words and stored word-location payloads retain independent dimensions.
The existing syntax-to-state store codec preserves every constructor and the
fixed five-bit Temp field, and has unconditional roundtrips in both directions.
-/

namespace Flapjack.Compiler.Backend.StackRemove
open Flapjack

/-- Reverse heap-list assertion for the complete ordered store list. Missing
keys become the original Word zero at the stored-value dimension; present
Word or Loc values pass through unchanged. The map is the canonical finite
map used by the faithful StackSem state, rather than an unrestricted lookup. -/
@[hol "cakeml/compiler/backend/proofs/stack_removeProofScript.sml" "word_store_def"
  (fmap_as_finite_support_relation := [store]) (words_as_type_indexed_bitvec)]
def wordStoreHOL {addressWidth : Nat} {valueWidth : Nat}
    [NeZero addressWidth] [NeZero valueWidth] (base : BitVec addressWidth)
    (store : HolFiniteMapExact WordStoreHOL (WordLocW valueWidth)) :
    ((BitVec addressWidth × WordLocW valueWidth) → Prop) → Prop :=
  wordListRev base (storeList.map fun name =>
    (store.lookup (StackSemRegisterTransfers.storeOfSyntax name)).getD (.word 0))

end Flapjack.Compiler.Backend.StackRemove

import Flapjack.HolRef
import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# word_alloc dead-code removal correctness

Counterpart of the dead-code removal section of `word_allocProofScript.sml`
(`live_store_rel_def` at line 3492, then `evaluate_remove_dead` and
`evaluate_remove_dead_prog`).
-/

namespace Flapjack.WordAlloc

/-- Exact HOL `live_store_rel_def` (`word_allocProofScript.sml:3492-3497`): the two
stores agree on every name outside the dead-store list. HOL `FLOOKUP` is `.lookup`
on the reviewed canonical finite-map carrier, and the two standalone maps are
recorded as bare relation-qualifier entries. -/
@[hol "cakeml/compiler/backend/proofs/word_allocProofScript.sml" "live_store_rel_def"
  (fmap_as_finite_support_relation := [sstore, tstore])]
def liveStoreRel {α β : Type} (nlive : List α) (sstore : HolFiniteMapExact α β)
    (tstore : HolFiniteMapExact α β) : Prop :=
  ∀ n, n ∉ nlive → sstore.lookup n = tstore.lookup n

end Flapjack.WordAlloc

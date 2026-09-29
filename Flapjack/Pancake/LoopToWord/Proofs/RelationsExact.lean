import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.Semantics.LoopSemStateExact
import Flapjack.Compiler.Backend.Semantics.WordSem.State

/-!
# `loop_to_wordProof` globals relation over the exact finite-map carriers

This is the exact port of `loop_to_wordProofScript.sml:27-30`'s
`globals_rel_def`. The source map is the `loopSem` state field
`5 word |-> word_loc`; the target is `wordSem`'s `store_name |-> word_loc`.
The target key is exactly `Temp n` from the imported `stackLang$store_name`
carrier. The relation is intentionally one-way and requires equality of the
stored `word_loc`; it makes no claim for target-only store entries. Both
finite-map arguments use the canonical `HolFiniteMapExact` rendering, and the
word payload uses the reviewed positive-width `BitVec` rendering.
-/

namespace Flapjack

/-- Exact HOL `globals_rel_def` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:27-30`:
every source global `(n,v)` must be present with the same value at the
WordSem `Temp n` key. Extra target store entries are unconstrained. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "globals_rel_def"
  (fmap_as_finite_support_relation := [g1, g2]) (words_as_type_indexed_bitvec)]
def loopToWordGlobalsRelHOLExact {width : Nat} [NeZero width]
    (g1 : HolFiniteMapExact (BitVec 5) (WordLocW width))
    (g2 : HolFiniteMapExact WordStoreHOL (WordLocW width)) : Prop :=
  ∀ n v, g1.lookup n = some v → g2.lookup (.temp n) = some v

end Flapjack

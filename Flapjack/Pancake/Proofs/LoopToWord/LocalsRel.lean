import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.WordLang

/-!
# Exact loop-to-word locals relation

The source is `locals_rel_def` at
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:19-24`. Its context and
both local environments are `sptree$num_map` values. This port uses the exact
`Spt` carrier and `sptLookup`/`sptMem`; local values use the exact
width-indexed `WordLocW` carrier. The only representation qualifier is the
standard HOL type-indexed word to `BitVec width` translation.
-/

namespace Flapjack.LoopToWord

/-- Exact HOL `loop_to_wordProof$locals_rel_def` over the HOL-shaped spt
carriers. The three clauses respectively require injective register assignment
on the context domain, nonzero even assigned registers, and lookup simulation
from each present source local to its mapped target register. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_def"
  (words_as_type_indexed_bitvec)]
def localsRelHOL {width : Nat} [NeZero width] (context : Spt Nat)
    (sourceLocals targetLocals : Spt (WordLocW width)) : Prop :=
  (∀ left right, sptMem left context → sptMem right context →
      findVarHOL context left = findVarHOL context right → left = right) ∧
  (∀ name register, sptLookup name context = some register →
      register ≠ 0 ∧ register % 2 = 0) ∧
  (∀ name value, sptLookup name sourceLocals = some value →
      ∃ register, sptLookup name context = some register ∧
        sptLookup register targetLocals = some value)

end Flapjack.LoopToWord

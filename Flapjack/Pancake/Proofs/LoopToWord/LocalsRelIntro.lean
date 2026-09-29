import Flapjack.Pancake.Proofs.LoopToWord.LocalsRel

/-!
# Exact Loop-to-Word `locals_rel_intro`

Ports `loop_to_wordProof$locals_rel_intro` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:129-135`.  HOL introduces the
three clauses of `locals_rel` (injective register assignment on the context
domain, nonzero even assigned registers, and lookup simulation) from the
relation.  The carriers are the exact `Spt` (`sptree$num_map`) context and
local environments and the exact width-indexed `WordLocW` local values, with
`find_var` rendered by the exact `findVarHOL`.
-/

namespace Flapjack.LoopToWord

/-- Exact HOL `loop_to_wordProof$locals_rel_intro`: the three defining clauses
of `localsRelHOL`, exposed as a conjunction. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "locals_rel_intro"
  (words_as_type_indexed_bitvec)]
theorem localsRelHOLIntro {width : Nat} [NeZero width]
    (context : Spt Nat) (sourceLocals targetLocals : Spt (WordLocW width))
    (hrel : localsRelHOL context sourceLocals targetLocals) :
    (∀ left right, sptMem left context → sptMem right context →
        findVarHOL context left = findVarHOL context right → left = right) ∧
    (∀ name register, sptLookup name context = some register →
        register ≠ 0 ∧ register % 2 = 0) ∧
    (∀ name value, sptLookup name sourceLocals = some value →
        ∃ register, sptLookup name context = some register ∧
          sptLookup register targetLocals = some value) :=
  hrel

end Flapjack.LoopToWord

import Flapjack.Pancake.LoopToWord
import Flapjack.Pancake.LoopToWord.CompFuncExact
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

/-- Exact HOL `globals_rel_intro` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:138-144`. It exposes the
same one-way lookup implication as `globals_rel_def`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "globals_rel_intro"
  (fmap_as_finite_support_relation := [g1, g2]) (words_as_type_indexed_bitvec)]
theorem loopToWordGlobalsRelIntroHOLExact {width : Nat} [NeZero width]
    (g1 : HolFiniteMapExact (BitVec 5) (WordLocW width))
    (g2 : HolFiniteMapExact WordStoreHOL (WordLocW width)) :
    loopToWordGlobalsRelHOLExact g1 g2 →
      ∀ n v, g1.lookup n = some v → g2.lookup (.temp n) = some v := by
  intro h n v hLookup
  exact h n v hLookup

/-- Exact HOL `code_rel_def` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:33-39`: every source code
entry `(params, body)` reached by `name` must be compiled to
`(LENGTH params + 1, comp_func name params body)` in the target code table,
and the parameter list must have no duplicates. The source code carrier is the
`loopSem` state's `funname |-> (varname list # prog)` as a reviewed
`Spt`, the target carrier is `wordSem`'s code `Spt` of
`Nat × WordLangProgHOL`, and the compiled body uses the exact
`loopToWordCompFuncHOL` port of HOL `comp_func`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "code_rel_def"
  (words_as_type_indexed_bitvec)]
def loopToWordCodeRelHOLExact {width : Nat} [NeZero width]
    (sourceCode : Spt (List Nat × HolLoopProg width))
    (targetCode : Spt (Nat × WordLangProgHOL (BitVec width))) : Prop :=
  ∀ name params body,
    sptLookup name sourceCode = some (params, body) →
      sptLookup name targetCode =
          some (params.length + 1, loopToWordCompFuncHOL name params body) ∧
        params.Nodup

end Flapjack

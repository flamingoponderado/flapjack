import Flapjack.Pancake.Semantics.LoopProps.CutSets

/-!
# Exact HOL `loopProps$comp_syntax_ok_def`

Counterpart of `cakeml/pancake/semantics/loopPropsScript.sml:57-73`. The
definition walks a `HolLoopProg` and checks that every live set recorded on a
`Loop`/`If` agrees with the set threaded by the syntax-directed `cut_sets`
analysis.

The `If` clause's set-extension condition is HOL's classical existential

```
EXISTS ns. nl = FOLDL (\sp n. insert n () sp) l ns
```

Because `Spt Unit` equality is structural (the derived `DecidableEq`) and
`FOLDL insert` can build a structurally different tree with the same keys, this
existential is *not* equivalent to a `sptSubsetLive` condition; it is rendered
literally here. The search is over `List Nat`, so there is no computable
decision procedure for a failing instance; the existential is decided by
`Classical.propDecidable`, supplied explicitly so the equality tests in the
other clauses keep the computable derived `DecidableEq` and reduce under `rfl`.
The definition is therefore `noncomputable`, exactly as HOL's genuinely
non-computable `EXISTS` is. The result stays `Bool`. -/

namespace Flapjack

/-- Exact HOL `comp_syntax_ok_def` (`loopPropsScript.sml:57-73`) over the
    faithful width-indexed `HolLoopProg` and `NumSet = Spt Unit` carriers. The
    `If` set-extension condition is HOL's classical existential over a
    `FOLDL` of `insert`, kept literally (see the module header); the definition
    is noncomputable because that existential has no computable decision
    procedure. The only carrier translation is HOL's positive word dimension to
    `BitVec width`. -/
@[hol "cakeml/pancake/semantics/loopPropsScript.sml" "comp_syntax_ok_def"
  (words_as_type_indexed_bitvec)]
noncomputable def compSyntaxOkHOL {width : Nat} [NeZero width] (live : NumSet) :
    HolLoopProg width → Bool
  | .skip => true
  | .assign _ _ => true
  | .loop liveIn body liveOut =>
      decide (live = liveIn) && decide (live = liveOut) &&
        compSyntaxOkHOL liveIn body
  | .arith _ => true
  | .break _ => true
  | .locValue _ _ => true
  | .load32 _ _ => true
  | .loadByte _ _ => true
  | .seq first second =>
      compSyntaxOkHOL live first && compSyntaxOkHOL (cutSetsHOL live first) second
  | .ite _ _ _ thenBranch elseBranch liveOut =>
      compSyntaxOkHOL live thenBranch && compSyntaxOkHOL live elseBranch &&
        @decide (∃ ns : List Nat, liveOut = ns.foldl (fun sp n => sptInsert n () sp) live)
          (Classical.propDecidable _)
  | _ => false

end Flapjack
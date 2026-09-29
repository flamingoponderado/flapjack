import Flapjack.Pancake.Semantics.LoopProps.AccVars

/-!
# Exact Loop-to-Word `acc_vars_acc'`

Ports the named theorem `acc_vars_acc'` from
`cakeml/pancake/proofs/loop_to_wordProofScript.sml:979-980`:

```
Theorem acc_vars_acc'[local] =
  acc_vars_acc |> CONV_RULE SWAP_FORALL_CONV |> SPEC "acc_vars (q:'a loopLang$prog) LN";
```

Specialising `loopProps$acc_vars_acc`
(`∀p l. domain (acc_vars p l) = domain (acc_vars p LN) ∪ domain l`, at
`loopPropsScript.sml:89`) at `l := acc_vars q LN` gives
`∀q p. domain (acc_vars p (acc_vars q LN)) =
   domain (acc_vars p LN) ∪ domain (acc_vars q LN)`, with `q` free and hence
universally quantified.  The Lean statement below is that statement over the
faithful width-indexed `HolLoopProg` carrier, using the exact `accVarsHOL`
(tagged `loopLangScript.sml:118-155`) and rendering the HOL sets by the
predicate `sptDomain` with union as pointwise disjunction.
-/

namespace Flapjack.LoopToWord

/-- Exact HOL `acc_vars_acc'`: the locals assigned by `p` when accumulated into
`acc_vars q LN` are exactly those `p` assigns into `LN` together with those `q`
assigns into `LN`. -/
@[hol "cakeml/pancake/proofs/loop_to_wordProofScript.sml" "acc_vars_acc'"
  (words_as_type_indexed_bitvec)]
theorem accVarsAccPrimeHOL {width : Nat} [NeZero width]
    (q p : HolLoopProg width) :
    sptDomain (accVarsHOL p (accVarsHOL q .ln)) =
      (fun k => sptDomain (accVarsHOL p .ln) k ∨ sptDomain (accVarsHOL q .ln) k) :=
  Flapjack.accVarsAccHOL p (accVarsHOL q .ln)

end Flapjack.LoopToWord

module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.MiniStateOps
public import Flapjack.Pancake.Semantics.LoopProps.NestedSeqSyntaxExact

@[expose] public section

/-! The bignum generator's compiled-code relations, ported from
`cakeml/compiler/backend/proofs/word_bignumProofScript.sml`. HOL's `ALOOKUP`
association-list lookup is the repository's `holAlookup`, which needs decidable
equality on the key type; HOL has equality for every type. -/
namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

/-- HOL `code_subset`: every entry of the first association list is present in
the second. The source's pair patterns are matched directly; its `n1` and `n2`
binder heads are vacuous and are discarded. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "code_subset_def"]
def codeSubset {α β γ δ : Type} [DecidableEq β] :
    α × List (β × γ) → δ × List (β × γ) → Prop
  | (_, cs1), (_, cs2) =>
      ∀ n v, holAlookup cs1 n = some v → holAlookup cs2 n = some v

/-- Code inclusion is reflexive. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "code_subset_refl" 368]
theorem codeSubset_refl {α β γ : Type} [DecidableEq β] (c1 : α × List (β × γ)) :
    codeSubset c1 c1 := by
  intro n v h
  exact h

/-- Code inclusion is reflexive. The source script declares this fact a second
time at line 2281; this theorem carries that declaration's line. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "code_subset_refl" 2281]
theorem codeSubset_refl_again {α β γ : Type} [DecidableEq β] (cs : α × List (β × γ)) :
    codeSubset cs cs :=
  codeSubset_refl cs

/-- Code inclusion is transitive. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "code_subset_trans"]
theorem codeSubset_trans {α β γ δ ε : Type} [DecidableEq β]
    (c1 : α × List (β × γ)) (c2 : δ × List (β × γ)) (c3 : ε × List (β × γ))
    (h12 : codeSubset c1 c2) (h23 : codeSubset c2 c3) : codeSubset c1 c3 := by
  intro n v h
  exact h23 n v (h12 n v h)

end Flapjack.Compiler.Backend.WordBignum

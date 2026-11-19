module

public import Flapjack.Compiler.Backend.WordBignum.Proofs.MiniStateOps
public import Flapjack.Pancake.Semantics.PanCommonProps.FiniteMapExact

@[expose] public section

/-! The finite-map library facts used by `word_bignumProofScript.sml`. The
bare `|->` map carriers are the reviewed `HolFiniteMapExact` translation, and
the standalone map parameter is recorded with the finite-support parameter
qualifier. -/

namespace Flapjack.Compiler.Backend.WordBignum

open Flapjack

/-- Canonical standalone-map witness for the exact `FLOOKUP_DOMSUB` parameter:
the reviewed broad-lookup codec roundtrips the canonical carrier. -/
theorem holFmapAsFiniteSupportParamWitness_FLOOKUP_DOMSUB_f {α β : Type}
    (f : HolFiniteMapExact β α) :
    holFiniteMapofBroad (holFiniteMaptoBroadlookup f) f.finiteSupport = f := by
  cases f
  rfl

/-- HOL `FLOOKUP_DOMSUB` (`word_bignumProofScript.sml:1621`): looking up a key
after domain subtraction is `NONE` at the removed key and the old lookup
elsewhere. HOL's `\\` is the equality-based domain subtraction of the carrier. -/
@[hol "cakeml/compiler/backend/proofs/word_bignumProofScript.sml" "FLOOKUP_DOMSUB"
  (fmap_as_finite_support_parameters := [f])]
theorem FLOOKUP_DOMSUB {α β : Type} [DecidableEq β]
    (f : HolFiniteMapExact β α) (n m : β) :
    (f.eraseEq n).lookup m = if m = n then none else f.lookup m :=
  rfl

end Flapjack.Compiler.Backend.WordBignum

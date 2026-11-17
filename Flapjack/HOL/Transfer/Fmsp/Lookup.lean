module

public import Flapjack.HOL.Transfer.Fmsp

@[expose] public section

/-! Lookup through the original sparse-tree to finite-map conversion. -/
namespace Flapjack.HOL.Transfer.Fmsp

@[hol "HOL/src/transfer/examples/fmspScript.sml" "FLOOKUP_sp2fm"
  (fmap_as_finite_support_result_observations := [Flapjack.HOL.Transfer.Fmsp.sp2fm])]
theorem flookupSp2fm {α : Type} (tree : Spt α) (key : Nat) :
    (sp2fm tree).lookup key = sptLookup key tree :=
  holFmapAsFiniteSupportResultWitness_sp2fm tree key

end Flapjack.HOL.Transfer.Fmsp

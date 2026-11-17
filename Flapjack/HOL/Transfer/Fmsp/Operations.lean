module

public import Flapjack.HOL.Transfer.Fmsp
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.FiniteMap.MapKeys

@[expose] public section

/-! Sparse-tree conversion commutes with empty trees and insertion. -/
namespace Flapjack.HOL.Transfer.Fmsp

@[hol "HOL/src/transfer/examples/fmspScript.sml" "sp2fm_thm"
  (fmap_as_finite_support_result_observations :=
    [Flapjack.HOL.Transfer.Fmsp.sp2fm, Flapjack.HolFiniteMapExact.holEmpty])]
theorem sp2fmThm {α β : Type} (k : Nat) (v : β) (tree : Spt β) :
    sp2fm (.ln : Spt α) = HolFiniteMapExact.holEmpty ∧
    sp2fm (sptInsert k v tree) = (sp2fm tree).updateEq (k, v) := by
  constructor
  · apply HolFiniteMapExact.ext_lookup
    intro x
    rfl
  · apply HolFiniteMapExact.ext_lookup
    intro x
    simp only [sp2fm, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL]
    by_cases hx : x = k
    · subst x
      simp [sptLookup_sptInsert_same]
    · simp [sptLookup_sptInsert_ne k x v tree hx, hx]

end Flapjack.HOL.Transfer.Fmsp

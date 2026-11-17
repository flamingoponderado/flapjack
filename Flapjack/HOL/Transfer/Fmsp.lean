module

public import Flapjack.Misc.Sptree
public import Flapjack.FiniteMap.Exact

@[expose] public section

/-! The original sparse-tree to finite-map conversion. -/
namespace Flapjack.HOL.Transfer.Fmsp

@[hol "HOL/src/transfer/examples/fmspScript.sml" "sp2fm_def" (fmap_as_finite_support_result)]
def sp2fm {α : Type} (tree : Spt α) : HolFiniteMapExact Nat α where
  lookup key := sptLookup key tree
  finiteSupport := by
    refine ⟨(sptToAList tree).map Prod.fst, ?_⟩
    intro key present
    cases found : sptLookup key tree with
    | none => exact (present found).elim
    | some value =>
      have hf := sptFoldi_lookup_mem tree 0 [] key value found
      have hm : (key, value) ∈ sptToAList tree := by
        simpa [sptToAList, sptAcc_eq, lrNext] using hf
      exact List.mem_map.mpr ⟨(key, value), hm, rfl⟩

/-- The converted map's lookup is the original sparse-tree lookup. -/
theorem holFmapAsFiniteSupportResultWitness_sp2fm {α : Type} (tree : Spt α) (key : Nat) :
    (sp2fm tree).lookup key = sptLookup key tree := rfl

end Flapjack.HOL.Transfer.Fmsp

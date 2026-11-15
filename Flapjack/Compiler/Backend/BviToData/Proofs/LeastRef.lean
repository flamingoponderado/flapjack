module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Build
public import Flapjack.FiniteMap.CardinalityExact
public import Flapjack.Misc.Sptree.Map

@[expose] public section

/-! Least-unused reference correspondence for constant construction. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- The canonical BVI reference map survives its broad-view codec. -/
theorem holFmapAsFiniteSupportParamWitness_refsRel_leastEq_bviRefs
    (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality bviRefs) bviRefs.finiteSupport).lookup key = bviRefs.lookup key ∧
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality bviRefs) bviRefs.finiteSupport).finiteSupport = bviRefs.finiteSupport ∧
    HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality bviRefs) bviRefs.finiteSupport = bviRefs := by
  cases bviRefs
  exact ⟨rfl, rfl, rfl⟩

/-- Lookup-related reference maps choose the same least unused index. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "refs_rel_LEAST_eq"
  (fmap_as_finite_support_parameters := [bviRefs])]
theorem refsRel_leastEq (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (dataRefs : Spt (BvlSem.Ref DataSem.Value))
    (related : ∀ key, bviRefs.lookup key = sptLookup key (sptMap dataToBviRef dataRefs)) :
    BvlSem.leastUnusedRef bviRefs = DataSem.leastUnusedRef dataRefs := by
  apply leastUnusedRef_projection dataRefs bviRefs
  intro key
  rw [← sptLookup_sptMap]
  exact related key

end Flapjack.Compiler.Backend.BviToData

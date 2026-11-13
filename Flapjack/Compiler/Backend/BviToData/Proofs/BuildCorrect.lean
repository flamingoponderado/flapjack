module

public import Flapjack.Compiler.Backend.BviToData.Proofs.Build
public import Flapjack.FiniteMap.CardinalityExact

@[expose] public section

/-! Source-statement correctness of constant construction. -/
namespace Flapjack.Compiler.Backend.BviToData
open Flapjack

/-- The canonical input reference map survives its broad-view codec. -/
theorem holFmapAsFiniteSupportParamWitness_doBuild_correct_bviRefs
    (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality bviRefs) bviRefs.finiteSupport).lookup key = bviRefs.lookup key ∧
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality bviRefs) bviRefs.finiteSupport).finiteSupport = bviRefs.finiteSupport ∧
    HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality bviRefs) bviRefs.finiteSupport = bviRefs := by
  cases bviRefs
  exact ⟨rfl, rfl, rfl⟩

/-- The canonical result reference map survives its broad-view codec. -/
theorem holFmapAsFiniteSupportParamWitness_doBuild_correct_bviNext
    (bviNext : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value)) (key : Nat) :
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality bviNext) bviNext.finiteSupport).lookup key = bviNext.lookup key ∧
    (HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality bviNext) bviNext.finiteSupport).finiteSupport = bviNext.finiteSupport ∧
    HolFiniteMapExact.ofBroadCardinality (HolFiniteMapExact.toBroadlookupCardinality bviNext) bviNext.finiteSupport = bviNext := by
  cases bviNext
  exact ⟨rfl, rfl, rfl⟩

/-- Corresponding environments and references produce corresponding builds. -/
@[hol "cakeml/compiler/backend/proofs/bvi_to_dataProofScript.sml" "do_build_thm"
  (fmap_as_finite_support_parameters := [bviRefs, bviNext])]
theorem doBuild_correct (parts : List ClosLang.ConstPart)
    (bviValues : Nat → BvlSem.Value) (dataValues : Nat → DataSem.Value) (index : Nat)
    (timestamp : Option Nat) (bviRefs : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (dataRefs : Spt (BvlSem.Ref DataSem.Value)) (result : BvlSem.Value)
    (bviNext : HolFiniteMapExact Nat (BvlSem.Ref BvlSem.Value))
    (run : BvlSem.doBuild bviValues index parts bviRefs = (result, bviNext))
    (refsRel : ∀ key, bviRefs.lookup key = (sptLookup key dataRefs).map dataToBviRef)
    (valuesRel : ∀ key, bviValues key = dataToBviValue (dataValues key)) :
    ∃ dataValue dataNext nextTimestamp,
      DataSem.doBuild dataValues index parts dataRefs timestamp = (dataValue, dataNext, nextTimestamp) ∧
      result = dataToBviValue dataValue ∧
      ∀ key, bviNext.lookup key = (sptLookup key dataNext).map dataToBviRef := by
  have projected := doBuild_projection parts dataValues bviValues index dataRefs bviRefs timestamp valuesRel refsRel
  rw [run] at projected
  cases dataRun : DataSem.doBuild dataValues index parts dataRefs timestamp with
  | mk dataValue dataTail =>
    obtain ⟨dataNext, nextTimestamp⟩ := dataTail
    refine ⟨dataValue, dataNext, nextTimestamp, rfl, ?_, ?_⟩
    · simpa [dataRun] using projected.1
    · simpa [dataRun] using projected.2

end Flapjack.Compiler.Backend.BviToData

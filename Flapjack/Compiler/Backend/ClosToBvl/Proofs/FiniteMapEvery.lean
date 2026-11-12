module

public import Flapjack.FiniteMap.BroadCodec
public import Flapjack.HolRef

@[expose] public section

/-! Finite-map predicate preservation for closure-to-BVL compilation. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- The finite-map input roundtrips through the canonical finite-support codec. -/
theorem holFmapAsFiniteSupportParamWitness_fEvery_fupdateList_suff_x {K V : Type}
    (x : HolFiniteMapExact K V) (key : K) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad x)).lookup key = x.lookup key ∧
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad x)).finiteSupport = x.finiteSupport ∧
    FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad x) = x := by
  cases x
  exact ⟨rfl, rfl, rfl⟩

open Classical in
/-- Updating a finite map with entries satisfying a predicate preserves that
predicate on all bindings. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "FEVERY_FUPDATE_LIST_SUFF"
  (fmap_as_finite_support_parameters := [x])]
theorem fEvery_fupdateList_suff {K V : Type} (progs : List (K × V))
    (x : HolFiniteMapExact K V) (p : K × V → Prop)
    (premises : (∀ key value, x.lookup key = some value → p (key, value)) ∧
      ∀ entry ∈ progs, p entry) :
    ∀ key value, (x.updateListEq progs).lookup key = some value → p (key, value) := by
  classical
  intro key value found
  rw [HolFiniteMapExact.lookup_updateListEq, FUPDATE_LIST_HOL_eq_FUPDATE_LIST] at found
  rcases flookupFupdateList_mem_or_base x.lookup progs key value found with
    ⟨entry, member, rfl, rfl⟩ | old
  · exact premises.2 entry member
  · exact premises.1 key value old

end Flapjack.Compiler.Backend.ClosToBvl

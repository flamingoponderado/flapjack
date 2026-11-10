module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.MakeState
public import Flapjack.FiniteMap.SubmapExact

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Finite-map update facts used by direct-call correctness. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

private def toBroad {K V : Type} (map : HolFiniteMapExact K V) : K → Option V := map.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- Canonical codec for the original finite-map parameter. -/
theorem holFmapAsFiniteSupportParamWitness_submap_updateList_f {A B : Type}
    (f : HolFiniteMapExact A B) (key : A) :
    (ofBroad (toBroad f) f.finiteSupport).lookup key = f.lookup key ∧
    (ofBroad (toBroad f) f.finiteSupport).finiteSupport = f.finiteSupport ∧
    ofBroad (toBroad f) f.finiteSupport = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

open Classical in
/-- Disjoint finite-map updates retain all original bindings. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "SUBMAP_FUPDATE_LIST"
  (fmap_as_finite_support_parameters := [f])]
theorem submap_updateList {A B : Type} (f : HolFiniteMapExact A B) (xs : List (A × B))
    (h : (xs.map Prod.fst).Nodup ∧ ∀ key, ¬ (key ∈ f.domain ∧ key ∈ xs.map Prod.fst)) :
    f.submap (f.updateListEq xs) := by
  intro key value found
  have outside : key ∉ xs.map Prod.fst := by
    intro member
    have inDomain : key ∈ f.domain := by simp [HolFiniteMapExact.domain, found]
    exact h.2 key ⟨inDomain, member⟩
  change FLOOKUP (FUPDATE_LIST_HOL f.lookup xs) key = some value
  rw [FLOOKUP_FUPDATE_LIST_HOL_not_mem f.lookup xs key outside]
  exact found

end Flapjack.Compiler.Backend.ClosCall

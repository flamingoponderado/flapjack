module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.MakeState
public import Flapjack.FiniteMap.SubmapExact
public import Flapjack.FiniteMap.BroadCodec
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.FiniteMap.UpdateListExact
public import Flapjack.FiniteMap.UnionExact
public import Flapjack.FiniteMap.MapKeys

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

/-- Lookup/support roundtrip for the finite-map input. -/
theorem holFmapAsFiniteSupportParamWitness_unionEmptyUpdateList_code {K V : Type}
    (code : HolFiniteMapExact K V) (key : K) :
    (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad code)).lookup key = code.lookup key ∧
      (FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad code)).finiteSupport = code.finiteSupport ∧
      FiniteMapBroad.ofBroad (FiniteMapBroad.toBroad code) = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Flapjack lookup infrastructure: equal input lookups stay equal after the same updates. -/
private theorem updateListLookupCongr {K V : Type} [DecidableEq K] (xs : List (K × V))
    (left right : FiniteMap K V) (key : K) (h : left key = right key) :
    FUPDATE_LIST_HOL left xs key = FUPDATE_LIST_HOL right xs key := by
  induction xs generalizing left right with
  | nil => exact h
  | cons entry rest ih =>
    rw [FUPDATE_LIST_HOL_cons, FUPDATE_LIST_HOL_cons]
    apply ih
    simp [FUPDATE_HOL, h]

/-- Disjoint updates agree with left-biased union, including repeated update keys. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "FUNION_FEMPTY_FUPDATE_LIST"
  (fmap_as_finite_support_parameter_observations :=
    (map_parameters := [code])
    (map_producers := [Flapjack.HolFiniteMapExact.union, Flapjack.HolFiniteMapExact.holEmpty,
      Flapjack.HolFiniteMapExact.holUpdateList]))]
theorem unionEmptyUpdateList {K V : Type} (code : HolFiniteMapExact K V) (aux : List (K × V))
    (disjoint : Disjoint code.domain {k | k ∈ aux.map Prod.fst}) :
    Flapjack.HolFiniteMapExact.union code
      (Flapjack.HolFiniteMapExact.holUpdateList Flapjack.HolFiniteMapExact.holEmpty aux) =
      Flapjack.HolFiniteMapExact.holUpdateList code aux := by
  classical
  apply HolFiniteMapExact.ext_lookup
  intro key
  simp only [HolFiniteMapExact.lookup_union, HolFiniteMapExact.holUpdateList,
    HolFiniteMapExact.lookup_updateListEq, HolFiniteMapExact.holEmpty]
  cases found : code.lookup key with
  | none => exact updateListLookupCongr aux _ _ key found.symm
  | some value =>
    have absent : key ∉ aux.map Prod.fst := by
      intro member
      have present : key ∈ code.domain := by simp [HolFiniteMapExact.domain, found]
      exact Set.disjoint_left.mp disjoint present member
    have keep := FLOOKUP_FUPDATE_LIST_HOL_not_mem code.lookup aux key absent
    change FUPDATE_LIST_HOL code.lookup aux key = code.lookup key at keep
    exact found.symm.trans keep.symm

end Flapjack.Compiler.Backend.ClosCall

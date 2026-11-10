module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
public import Flapjack.FiniteMap.AlistExact
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.Misc.Option
public import Flapjack.Misc.Sptree.ToAList

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Construct direct-call compiler states from a sparse map and code. -/
namespace Flapjack.Compiler.Backend.ClosCall
open Flapjack

private def toBroad {K V : Type} (code : HolFiniteMapExact K V) : K → Option V := code.lookup
private def ofBroad {K V : Type} (lookup : K → Option V)
    (support : ∃ keys : List K, ∀ key, lookup key ≠ none → key ∈ keys) : HolFiniteMapExact K V :=
  ⟨lookup, support⟩

/-- The code parameter uses the canonical finite-map codec. -/
theorem holFmapAsFiniteSupportParamWitness_makeState_code {B : Type}
    (code : HolFiniteMapExact Nat B) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code := by
  cases code
  exact ⟨rfl, rfl, rfl⟩

/-- Construct the auxiliary code list when every known location has code. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "make_g_def"
  (fmap_as_finite_support_parameters := [code])]
noncomputable def makeState {A B : Type} [Nonempty B] (d : Spt A)
    (code : HolFiniteMapExact Nat B) : Option (Spt A × List (Nat × B)) := by
  classical
  exact if Set.image Nat.succ (sptDomain d) ⊆ code.domain then
    some (d, (sptToAList d).map (fun entry => (entry.1 + 1, holThe (code.lookup (entry.1 + 1)))))
  else none

/-- The code parameter in makeState well-formedness uses the canonical codec. -/
theorem holFmapAsFiniteSupportParamWitness_makeState_wellFormed_code {B : Type}
    (code : HolFiniteMapExact Nat B) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_makeState_code code key

/-- Every state produced by makeState satisfies the full compiler-state invariant. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "make_g_wfg"
  (fmap_as_finite_support_parameters := [code])]
theorem makeState_wellFormed {A B : Type} [Nonempty B] (d : Spt A)
    (code : HolFiniteMapExact Nat B) (g : Spt A × List (Nat × B))
    (h : makeState d code = some g) : wellFormed g := by
  classical
  unfold makeState at h
  split at h
  next valid =>
    simp only [Option.some.injEq] at h
    subst g
    constructor
    · funext key
      apply propext
      simp only [List.map_map, List.mem_map, Function.comp_def]
      constructor
      · rintro ⟨⟨loc, value⟩, member, eq⟩
        refine ⟨loc, ?_, ?_⟩
        · exact (sptDomain_iff_lookup d loc).2 ⟨value, (sptMemToAList d loc value).1 member⟩
        · simpa [Nat.succ_eq_add_one] using eq
      · rintro ⟨loc, member, eq⟩
        obtain ⟨value, found⟩ := (sptDomain_iff_lookup d loc).1 member
        refine ⟨(loc, value), (sptMemToAList d loc value).2 found, ?_⟩
        simpa [Nat.succ_eq_add_one] using eq
    · have distinct := sptAllDistinctMapFstToAList d
      have shifted : (((sptToAList d).map Prod.fst).map (fun k => k + 1)).Nodup :=
        (List.nodup_map_iff (fun _ _ eq => Nat.add_right_cancel eq)).2 distinct
      simpa [List.map_map, Function.comp_def] using shifted
  next invalid => simp at h

private theorem fupdateList_of_distinct_member {K V : Type} [DecidableEq K]
    (base : FiniteMap K V) (entries : List (K × V)) (key : K) (value : V)
    (h : (entries.map Prod.fst).Nodup ∧ (key, value) ∈ entries) :
    FUPDATE_LIST_HOL base entries key = some value := by
  induction entries generalizing base with
  | nil => simp at h
  | cons entry tail ih =>
    obtain ⟨k, v⟩ := entry
    simp only [List.map_cons, List.nodup_cons, List.mem_cons, Prod.mk.injEq] at h
    obtain ⟨⟨fresh, distinct⟩, member⟩ := h
    rw [FUPDATE_LIST_HOL_cons]
    rcases member with ⟨rfl, rfl⟩ | member
    · have unchanged := FLOOKUP_FUPDATE_LIST_HOL_not_mem (FUPDATE_HOL base (key, value)) tail key fresh
      simpa [FLOOKUP, FUPDATE_HOL] using unchanged
    · exact ih (FUPDATE_HOL base (k, v)) ⟨distinct, member⟩

/-- Constructing a state from its own well-formed auxiliary code extends it. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "make_g_subg"
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.alistToFmap])]
theorem makeState_subg {A B : Type} [Nonempty B] (cfg : Spt A)
    (aux : List (Nat × B)) (newState : Spt A × List (Nat × B))
    (h : makeState cfg (HolFiniteMapExact.alistToFmap aux.reverse) = some newState ∧
      wellFormed (cfg, aux)) : stateExtends (cfg, aux) newState := by
  classical
  obtain ⟨run, well⟩ := h
  have mapEq : HolFiniteMapExact.alistToFmap aux.reverse = HolFiniteMapExact.empty.updateListEq aux := by
    simp only [HolFiniteMapExact.alistToFmap, List.reverse_reverse]
    congr 1
    exact Subsingleton.elim _ _
  rw [mapEq] at run
  have newWell := makeState_wellFormed cfg (HolFiniteMapExact.empty.updateListEq aux) newState run
  have distinct := well.2
  unfold makeState at run
  split at run
  next valid =>
    simp only [Option.some.injEq] at run
    subst newState
    refine ⟨?_, ?_, newWell.2⟩
    · intro key member
      exact ⟨member, rfl⟩
    · intro key value found
      have pairMember := holALookup_member aux key value found
      have keyMember : key ∈ aux.map Prod.fst := List.mem_map.mpr ⟨(key, value), pairMember, rfl⟩
      have domain : key ∈ Set.image Nat.succ (sptDomain cfg) := by
        rw [← well.1]
        exact keyMember
      obtain ⟨index, indomain, keyEq⟩ := domain
      obtain ⟨sparseValue, sparseLookup⟩ := (sptDomain_iff_lookup cfg index).1 indomain
      have originalLookup : (HolFiniteMapExact.empty.updateListEq aux).lookup key = some value := by
        exact fupdateList_of_distinct_member _ aux key value ⟨distinct, pairMember⟩
      have member : (key, value) ∈ (sptToAList cfg).map
          (fun entry => (entry.1 + 1, holThe ((HolFiniteMapExact.empty.updateListEq aux).lookup (entry.1 + 1)))) := by
        apply List.mem_map.mpr
        refine ⟨(index, sparseValue), (sptMemToAList cfg index sparseValue).2 sparseLookup, ?_⟩
        have keyEq' : index + 1 = key := by omega
        change (index + 1, holThe ((HolFiniteMapExact.empty.updateListEq aux).lookup (index + 1))) = (key, value)
        rw [keyEq', originalLookup]
        rfl
      exact holALookup_of_distinct_member _ key value ⟨newWell.2, member⟩
  next invalid => simp at run

end Flapjack.Compiler.Backend.ClosCall

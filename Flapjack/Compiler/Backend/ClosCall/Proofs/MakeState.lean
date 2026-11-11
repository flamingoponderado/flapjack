module

public import Flapjack.Compiler.Backend.ClosCall.Proofs.Wellformed
public import Flapjack.Compiler.Backend.ClosCall.Proofs.StateExtension
public import Flapjack.FiniteMap.AlistExact
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.FiniteMap.EmptyExact
public import Flapjack.FiniteMap.UpdateListExact
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

/-- Incrementing the first components preserves list distinctness. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "ALL_DISTINCT_MAP_FST_ADD1"]
theorem distinctMapFstAdd1 {A : Type} (xs : List (Nat × A)) :
    (xs.map (fun k => k.1 + 1)).Nodup ↔ (xs.map Prod.fst).Nodup := by
  simpa [List.map_map, Function.comp_def] using
    (List.nodup_map_iff (l := xs.map Prod.fst) (fun _ _ eq => Nat.add_right_cancel eq))

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
      simpa [List.map_map, Function.comp_def] using (distinctMapFstAdd1 _).2 distinct
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
  (fmap_as_finite_support_result_observations := [Flapjack.HolFiniteMapExact.holEmpty, Flapjack.HolFiniteMapExact.holUpdateList])]
theorem makeState_subg {A B : Type} [Nonempty B] (cfg : Spt A)
    (aux : List (Nat × B)) (newState : Spt A × List (Nat × B))
    (h : makeState cfg (HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty aux) = some newState ∧
      wellFormed (cfg, aux)) : stateExtends (cfg, aux) newState := by
  classical
  obtain ⟨run, well⟩ := h
  have mapEq : HolFiniteMapExact.holUpdateList HolFiniteMapExact.holEmpty aux =
      HolFiniteMapExact.empty.updateListEq aux := by
    simp only [HolFiniteMapExact.holUpdateList, HolFiniteMapExact.holEmpty]
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

/-- Canonical codec for the first code map in state-construction uniqueness. -/
theorem holFmapAsFiniteSupportParamWitness_makeState_eq_x2 {B : Type}
    (x2 : HolFiniteMapExact Nat B) (key : Nat) :
    (ofBroad (toBroad x2) x2.finiteSupport).lookup key = x2.lookup key ∧
    (ofBroad (toBroad x2) x2.finiteSupport).finiteSupport = x2.finiteSupport ∧
    ofBroad (toBroad x2) x2.finiteSupport = x2 :=
  holFmapAsFiniteSupportParamWitness_makeState_code x2 key

/-- Canonical codec for the second code map in state-construction uniqueness. -/
theorem holFmapAsFiniteSupportParamWitness_makeState_eq_y2 {B : Type}
    (y2 : HolFiniteMapExact Nat B) (key : Nat) :
    (ofBroad (toBroad y2) y2.finiteSupport).lookup key = y2.lookup key ∧
    (ofBroad (toBroad y2) y2.finiteSupport).finiteSupport = y2.finiteSupport ∧
    ofBroad (toBroad y2) y2.finiteSupport = y2 :=
  holFmapAsFiniteSupportParamWitness_makeState_code y2 key

/-- Constructed states with the same sparse tree and an extension relation agree. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "make_g_make_g_eq"
  (fmap_as_finite_support_parameters := [x2, y2])]
theorem makeState_eq {A B : Type} [Nonempty B]
    (x1 : Spt A) (x2 : HolFiniteMapExact Nat B)
    (y1 : Spt A) (y2 : HolFiniteMapExact Nat B)
    (g0 g1 : Spt A × List (Nat × B))
    (h : g0.1 = g1.1 ∧ stateExtends g0 g1 ∧
      makeState x1 x2 = some g0 ∧ makeState y1 y2 = some g1) : g0 = g1 := by
  classical
  obtain ⟨sameTree, extension, run0, run1⟩ := h
  have wf0 := makeState_wellFormed x1 x2 g0 run0
  have wf1 := makeState_wellFormed y1 y2 g1 run1
  unfold makeState at run0 run1
  split at run0 <;> try contradiction
  split at run1 <;> try contradiction
  simp only [Option.some.injEq] at run0 run1
  subst g0
  subst g1
  simp only at sameTree
  subst y1
  simp only [Prod.mk.injEq, true_and]
  apply List.map_congr_left
  intro entry member
  obtain ⟨k, v⟩ := entry
  have mem0 : (k + 1, holThe (x2.lookup (k + 1))) ∈
      (sptToAList x1).map (fun entry => (entry.1 + 1, holThe (x2.lookup (entry.1 + 1)))) :=
    List.mem_map.mpr ⟨(k, v), member, rfl⟩
  have mem1 : (k + 1, holThe (y2.lookup (k + 1))) ∈
      (sptToAList x1).map (fun entry => (entry.1 + 1, holThe (y2.lookup (entry.1 + 1)))) :=
    List.mem_map.mpr ⟨(k, v), member, rfl⟩
  have lookup0 := holALookup_of_distinct_member _ _ _ ⟨wf0.2, mem0⟩
  have lookup1 := holALookup_of_distinct_member _ _ _ ⟨wf1.2, mem1⟩
  have same := (extension.2.1 _ _ lookup0).symm.trans lookup1
  exact congrArg (fun value => (k + 1, value)) (Option.some.inj same)

private theorem makeState_get {A B : Type} [Nonempty B] (tree : Spt A)
    (code : HolFiniteMapExact Nat B) (state : Spt A × List (Nat × B))
    (index : Nat) (value : B) (run : makeState tree code = some state)
    (inTree : sptDomain tree index) (found : code.lookup (index + 1) = some value) :
    holALookup state.2 (index + 1) = some value := by
  classical
  have well := makeState_wellFormed tree code state run
  unfold makeState at run
  split at run <;> try contradiction
  simp only [Option.some.injEq] at run
  subst state
  obtain ⟨sparseValue, sparseLookup⟩ := (sptDomain_iff_lookup tree index).1 inTree
  apply holALookup_of_distinct_member
  refine ⟨well.2, ?_⟩
  apply List.mem_map.mpr
  refine ⟨(index, sparseValue), (sptMemToAList tree index sparseValue).2 sparseLookup, ?_⟩
  change (index + 1, holThe (code.lookup (index + 1))) = (index + 1, value)
  rw [found]
  rfl

private theorem makeState_code {A B : Type} [Nonempty B] (tree : Spt A)
    (code : HolFiniteMapExact Nat B) (state : Spt A × List (Nat × B))
    (key : Nat) (value : B) (run : makeState tree code = some state)
    (found : holALookup state.2 key = some value) : code.lookup key = some value := by
  classical
  unfold makeState at run
  split at run
  next valid =>
    simp only [Option.some.injEq] at run
    subst state
    have member := holALookup_member _ key value found
    obtain ⟨⟨index, sparseValue⟩, inList, pairEq⟩ := List.mem_map.mp member
    have inTree : sptDomain tree index :=
      (sptDomain_iff_lookup tree index).2 ⟨sparseValue, (sptMemToAList tree index sparseValue).1 inList⟩
    have inCode : index + 1 ∈ code.domain := valid ⟨index, inTree, by omega⟩
    have ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
    change code.lookup (index + 1) ≠ none at inCode
    cases h : code.lookup (index + 1) with
    | none => contradiction
    | some v => simp [holThe]
  next invalid => simp at run
/-- Canonical finite-map codec for the source code map. -/
theorem holFmapAsFiniteSupportParamWitness_makeState_imp_subg_code {B : Type}
    (code : HolFiniteMapExact Nat B) (key : Nat) :
    (ofBroad (toBroad code) code.finiteSupport).lookup key = code.lookup key ∧
    (ofBroad (toBroad code) code.finiteSupport).finiteSupport = code.finiteSupport ∧
    ofBroad (toBroad code) code.finiteSupport = code :=
  holFmapAsFiniteSupportParamWitness_makeState_code code key

/-- New disjoint code and an extended sparse tree produce a state extending
both the new programs and the earlier constructed state. -/
@[hol "cakeml/compiler/backend/proofs/clos_callProofScript.sml" "make_g_IMP_subg"
  (fmap_as_finite_support_parameters := [code])]
theorem makeState_imp_subg {B : Type} [Nonempty B] (r0 : NumSet)
    (code : HolFiniteMapExact Nat B) (g0 : NumSet × List (Nat × B))
    (progs1 : List (Nat × B)) (r1 : NumSet) (g1 : NumSet × List (Nat × B))
    (h : makeState r0 code = some g0 ∧
      (∀ k, ¬ (k ∈ code.domain ∧ k ∈ progs1.map Prod.fst)) ∧
      (progs1.map Prod.fst).Nodup ∧
      makeState r1 (code.updateListEq progs1) = some g1 ∧
      sptSubspt r0 r1 ∧
      (∀ k ∈ progs1.map Prod.fst, k ∈ Set.image Nat.succ (sptDomain r1))) :
    stateExtends (r1, progs1 ++ g0.2) g1 := by
  classical
  obtain ⟨run0, disjoint, distinct, run1, sub, inDomain⟩ := h
  have well0 := makeState_wellFormed r0 code g0 run0
  have well1 := makeState_wellFormed r1 (code.updateListEq progs1) g1 run1
  have tree1 : g1.1 = r1 := by
    unfold makeState at run1
    split at run1
    next _ =>
      simp only [Option.some.injEq] at run1
      exact (congrArg Prod.fst run1).symm
    next _ => simp at run1
  refine ⟨?_, ?_, well1.2⟩
  · rw [tree1]
    exact fun key member => ⟨member, rfl⟩
  · intro key value found
    rw [holALookup_append] at found
    cases program : holALookup progs1 key with
    | some v =>
      simp [program] at found
      subst v
      have pair := holALookup_member progs1 key value program
      have mem : key ∈ progs1.map Prod.fst := List.mem_map.mpr ⟨(key, value), pair, rfl⟩
      obtain ⟨index, inTree, keyEq⟩ := inDomain key mem
      have lookup : (code.updateListEq progs1).lookup key = some value :=
        fupdateList_of_distinct_member code.lookup progs1 key value ⟨distinct, pair⟩
      have keyEq' : index + 1 = key := by omega
      rw [← keyEq'] at lookup ⊢
      exact makeState_get r1 _ g1 index value run1 inTree lookup
    | none =>
      simp [program] at found
      have oldLookup := makeState_code r0 code g0 key value run0 found
      have oldKey : key ∈ g0.2.map Prod.fst :=
        List.mem_map.mpr ⟨(key, value), holALookup_member g0.2 key value found, rfl⟩
      have oldDomain : key ∈ Set.image Nat.succ (sptDomain g0.1) := by rw [← well0.1]; exact oldKey
      have tree0 : g0.1 = r0 := by
        unfold makeState at run0
        split at run0
        next _ =>
          simp only [Option.some.injEq] at run0
          exact (congrArg Prod.fst run0).symm
        next _ => simp at run0
      rw [tree0] at oldDomain
      obtain ⟨index, oldTree, keyEq⟩ := oldDomain
      have newTree : sptDomain r1 index := (sub index oldTree).1
      have notProgram : key ∉ progs1.map Prod.fst := by
        intro mem
        have codeMem : key ∈ code.domain := by simp [HolFiniteMapExact.domain, oldLookup]
        exact disjoint key ⟨codeMem, mem⟩
      have lookup : (code.updateListEq progs1).lookup key = some value := by
        change FUPDATE_LIST_HOL code.lookup progs1 key = some value
        have eq := FLOOKUP_FUPDATE_LIST_HOL_not_mem code.lookup progs1 key notProgram
        change FUPDATE_LIST_HOL code.lookup progs1 key = code.lookup key at eq
        exact eq.trans oldLookup
      have keyEq' : index + 1 = key := by omega
      rw [← keyEq'] at lookup ⊢
      exact makeState_get r1 _ g1 index value run1 newTree lookup


end Flapjack.Compiler.Backend.ClosCall

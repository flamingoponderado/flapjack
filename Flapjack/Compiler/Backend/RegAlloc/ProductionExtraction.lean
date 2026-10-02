import Flapjack.Compiler.Backend.RegAlloc.ProductionColouring
import Flapjack.Compiler.Backend.RegAlloc.ProductionColourLookup
import Flapjack.Compiler.Backend.RegAlloc.Proofs.ColourExtraction

namespace Flapjack.RegAlloc
open RiscV RiscV.CakeRegAlloc Translator.Monadic.MonadBase

private theorem lookup_member (entries : NatInfoMap Nat) (key value : Nat)
    (found : lookupNatInfo key entries = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp [lookupNatInfo] at found
  | cons entry rest ih =>
    obtain ⟨other, stored⟩ := entry
    simp only [lookupNatInfo, Bool.beq_eq_decide_eq] at found
    by_cases equal : other = key
    · subst other
      simp at found
      subst stored
      exact List.mem_cons_self
    · simp [equal] at found
      exact List.mem_cons_of_mem _ (ih found)

private theorem lookup_first (key : Nat) (entries : NatInfoMap Nat) :
    lookupNatInfo key entries = sptAListLookup key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨other, value⟩ := entry
    simp only [lookupNatInfo, sptAListLookup, Bool.beq_eq_decide_eq]
    by_cases equal : key = other
    · subst other
      simp
    · simp [equal, Ne.symm equal, ih]

/-- Actual sorted extraction preserves both present and absent source-name
lookups. Name uniqueness is proved by the executed mkBij producer. Untagged
Flapjack infrastructure rather than another HOL extraction declaration. -/
theorem extractColor_lookup_all (tree : WordClashTree) (production : CakeRaState) (name : Nat) :
    lookupNatInfo name (cakeExtractColor production (cakeMkBij tree).toAllocator) =
      (lookupNatInfo name (cakeMkBij tree).toAllocator).map (cakeTagCol production) := by
  cases found : lookupNatInfo name (cakeMkBij tree).toAllocator with
  | some node =>
    simpa only [found, Option.map_some] using
      Flapjack.extractColor_lookup tree production name node (lookup_member _ _ _ found)
  | none =>
    cases colour : lookupNatInfo name (cakeExtractColor production (cakeMkBij tree).toAllocator) with
    | none => rfl
    | some value =>
      have member := lookup_member _ _ _ colour
      simp only [cakeExtractColor, List.mem_map] at member
      obtain ⟨⟨source, node⟩, sortedMember, equal⟩ := member
      have sourceMember := (List.mergeSort_perm (cakeMkBij tree).toAllocator
        (fun a b => a.1 < b.1)).mem_iff.mp sortedMember
      have sourceEq : source = name := congrArg Prod.fst equal
      subst source
      have lookup := Flapjack.mkBij_forward_lookup tree name node sourceMember
      rw [found] at lookup
      contradiction

private theorem tagColour_production (node : Nat) {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (bound : node < native.node_tag.length) :
    cakeTagCol production node = extractTag (holEl node native.node_tag) := by
  rw [holEl_eq_getElem node native.node_tag bound]
  simp only [cakeTagCol, related.tag_read node bound]
  cases native.node_tag[node] <;> rfl

/-- Full native extraction succeeds with exactly the canonical map of the
executed output from the real produced bijection. All source-name lookups,
including absent names, agree. Bounds and uniqueness come from actual mkBij;
the dimension equality links its initialization domain to the original state.
This is untagged actual/native infrastructure. Original/native whole mkBij,
graph and tag initialization correspondence remains a separate prerequisite. -/
theorem extractColor_production (tree : WordClashTree)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (dimension : (cakeMkBij tree).nextNode = native.dim) :
    extractColor (sptFromAList (cakeMkBij tree).toAllocator) native =
      (.success (sptFromAList (cakeExtractColor production (cakeMkBij tree).toAllocator)), native) := by
  have bounds : ∀ name node,
      sptLookup name (sptFromAList (cakeMkBij tree).toAllocator) = some node → node < native.dim := by
    intro name node found
    rw [sptLookup_sptFromAList, ← lookup_first] at found
    rw [← dimension]
    exact Flapjack.mkBij_bounds tree _ (lookup_member _ _ _ found)
  rw [extractColorSucceeds native _ ⟨good, bounds, sptWfFromAList _⟩]
  congr 2
  apply (sptEqThm _ _ ⟨by rw [sptWfMap]; exact sptWfFromAList _, sptWfFromAList _⟩).mpr
  intro name
  rw [sptLookup_sptMap, sptLookup_sptFromAList, sptLookup_sptFromAList,
    ← lookup_first, ← lookup_first, extractColor_lookup_all]
  cases found : lookupNatInfo name (cakeMkBij tree).toAllocator with
  | none => rfl
  | some node =>
    have bound : node < native.node_tag.length := by
      rw [good.2.1, ← dimension]
      exact Flapjack.mkBij_bounds tree _ (lookup_member _ _ _ found)
    simp only [Option.map_some, tagColour_production node related bound]

/-- Complete executed move-table/colouring/extraction slice, returning the
actual output map and native final state. Input state correspondence and the
initialization dimension are the genuine remaining producer boundary; no
supplied output map, post-state relation or target execution is assumed.
This is Flapjack cross-implementation infrastructure without a HOL tag. -/
theorem colouringExtract_production (tree : WordClashTree) (limit : Nat)
    (moves : List (Nat × (Nat × Nat))) (nodes : List Nat)
    {native : State} {production : CakeRaState}
    (related : ProductionStateRel native production) (good : goodRaState native)
    (dimension : (cakeMkBij tree).nextNode = native.dim) :
    ∃ result,
      let table := resortMoves (movesToSp moves .ln)
      let actualTable := cakeResortMovesSp
        (cakeMovesToSp moves (CakeNodeMap.ofSize (cakeMkBij tree).nextNode))
      let actualFinal := cakeAssignStemps limit
        (fun s n bads => cakeNegBiasedPref s limit actualTable n bads)
        (cakeAssignAtemps limit nodes (fun s n ks => cakeBiasedPref s actualTable n ks) production)
      ignoreBind (assignAtemps limit nodes (biasedPref table))
        (ignoreBind (assignStemps limit (negBiasedPref limit table))
          (extractColor (sptFromAList (cakeMkBij tree).toAllocator))) native =
        (.success (sptFromAList (cakeExtractColor actualFinal (cakeMkBij tree).toAllocator)), result) ∧
      goodRaState result ∧ native.dim = result.dim ∧ ProductionStateRel result actualFinal := by
  obtain ⟨result, run, resultGood, resultDim, resultRel⟩ :=
    colouring_production (cakeMkBij tree).nextNode limit moves nodes related good
  have extracted := extractColor_production tree resultRel resultGood (dimension.trans resultDim)
  refine ⟨result, ?_, resultGood, resultDim, resultRel⟩
  have compose : ∀ (a b : M State Unit StateException) (c : M State (Spt Nat) StateException),
      ignoreBind a (ignoreBind b c) native = ignoreBind (ignoreBind a b) c native := by
    intro a b c
    simp only [ignoreBind]
    cases a native with
    | mk outcome state => cases outcome with
      | failure error => rfl
      | success value => cases b state with
        | mk outcome state => cases outcome <;> rfl
  rw [compose]
  simp only [ignoreBind] at run
  simp only [ignoreBind, run, extracted]

end Flapjack.RegAlloc

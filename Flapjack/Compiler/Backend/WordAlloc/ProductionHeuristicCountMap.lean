import Flapjack.Compiler.Backend.WordAlloc.ProductionTreeMapMerge
import Flapjack.Compiler.Backend.WordAlloc.HeuMax
import Flapjack.Misc.Sptree.MapiLookup

namespace Flapjack.WordAlloc
open RiscV

/-! Actual TreeMap counter-state transport. The canonical codec is derived
from the real map, not supplied as a post-state premise. This infrastructure
has no independent HOL original. Actual branch maxAll and the complete
heuristic program producer remain separate obligations. -/

def heuristicCountMapToNative (counts : WordHeuristicCountMap) : Spt HeuData :=
  sptFromAList (counts.entries.toList.map (fun entry =>
    (entry.1, heuristicCountsToNative entry.2)))

private theorem assocAbsent {α : Type} (entries : List (Nat × α)) (key : Nat)
    (missing : key ∉ entries.map Prod.fst) : sptAListLookup key entries = none := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      have parts : key ≠ name ∧ key ∉ rest.map Prod.fst := by simpa using missing
      simp only [sptAListLookup, parts.1, if_false, ih parts.2]

private theorem assocTreeMap {α : Type} (tree : Std.TreeMap Nat α) (key : Nat) :
    sptAListLookup key tree.toList = tree[key]? := by
  cases found : tree[key]? with
  | none =>
      apply assocAbsent
      simp only [Std.TreeMap.map_fst_toList_eq_keys, Std.TreeMap.mem_keys]
      intro member
      have present := Std.TreeMap.mem_iff_isSome_getElem?.mp member
      simp [found] at present
  | some value =>
      apply sptAListLookup_eq_of_mem_unique key value tree.toList
      · exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr found
      · intro other member
        have same := Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp member
        rw [found] at same
        exact (Option.some.inj same).symm

private theorem assocPayloadMap {α β : Type} (f : α → β)
    (entries : List (Nat × α)) (key : Nat) :
    sptAListLookup key (entries.map (fun entry => (entry.1, f entry.2))) =
      (sptAListLookup key entries).map f := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      by_cases same : key = name <;> simp [sptAListLookup, same, ih]

theorem heuristicCountMap_lookup (counts : WordHeuristicCountMap) (key : Nat) :
    sptLookup key (heuristicCountMapToNative counts) =
      (counts.lookup key).map heuristicCountsToNative := by
  rw [heuristicCountMapToNative, sptLookup_sptFromAList, assocPayloadMap, assocTreeMap]
  rfl

theorem heuristicCountMap_wf (counts : WordHeuristicCountMap) :
    sptWf (heuristicCountMapToNative counts) = true := sptWfFromAList _

theorem heuristicCountMap_update (counts : WordHeuristicCountMap) (name : Nat)
    (update : WordHeuristicCounts → WordHeuristicCounts) :
    heuristicCountMapToNative (counts.update name update) =
      sptInsert name (heuristicCountsToNative
        (update ((counts.lookup name).getD wordHeuristicZero)))
        (heuristicCountMapToNative counts) := by
  apply (sptEqThm _ _ ⟨heuristicCountMap_wf _,
    sptWfInsert _ _ _ (heuristicCountMap_wf _)⟩).mpr
  intro key
  by_cases same : key = name
  · subst key
    rw [sptLookup_sptInsert_same, heuristicCountMap_lookup]
    simp [WordHeuristicCountMap.lookup, WordHeuristicCountMap.update]
  · rw [sptLookup_sptInsert_ne name key _ _ same,
      heuristicCountMap_lookup, heuristicCountMap_lookup]
    have different : compare name key ≠ Ordering.eq := by
      intro equal
      exact same (Std.LawfulEqCmp.compare_eq_iff_eq.mp equal).symm
    simp [WordHeuristicCountMap.lookup, WordHeuristicCountMap.update,
      Std.TreeMap.getElem?_alter, different]

theorem heuristicCountMap_addLhsConst (counts : WordHeuristicCountMap) (name : Nat) :
    heuristicCountMapToNative (counts.addLhsConst name) =
      add1LhsConst name (heuristicCountMapToNative counts) := by
  rw [WordHeuristicCountMap.addLhsConst, heuristicCountMap_update]
  unfold add1LhsConst
  rw [heuristicCountMap_lookup]
  cases found : counts.lookup name <;> simp [heuristicCountsToNative, wordHeuristicZero]

theorem heuristicCountMap_addLhsReg (counts : WordHeuristicCountMap) (name : Nat) :
    heuristicCountMapToNative (counts.addLhsReg name) =
      add1LhsReg name (heuristicCountMapToNative counts) := by
  rw [WordHeuristicCountMap.addLhsReg, heuristicCountMap_update]
  unfold add1LhsReg
  rw [heuristicCountMap_lookup]
  cases found : counts.lookup name <;> simp [heuristicCountsToNative, wordHeuristicZero]

theorem heuristicCountMap_addLhsMem (counts : WordHeuristicCountMap) (name : Nat) :
    heuristicCountMapToNative (counts.addLhsMem name) =
      add1LhsMem name (heuristicCountMapToNative counts) := by
  rw [WordHeuristicCountMap.addLhsMem, heuristicCountMap_update]
  unfold add1LhsMem
  rw [heuristicCountMap_lookup]
  cases found : counts.lookup name <;> simp [heuristicCountsToNative, wordHeuristicZero]

theorem heuristicCountMap_addRhsReg (counts : WordHeuristicCountMap) (name : Nat) :
    heuristicCountMapToNative (counts.addRhsReg name) =
      add1RhsReg name (heuristicCountMapToNative counts) := by
  rw [WordHeuristicCountMap.addRhsReg, heuristicCountMap_update]
  unfold add1RhsReg
  rw [heuristicCountMap_lookup]
  cases found : counts.lookup name <;> simp [heuristicCountsToNative, wordHeuristicZero]

theorem heuristicCountMap_addRhsMem (counts : WordHeuristicCountMap) (name : Nat) :
    heuristicCountMapToNative (counts.addRhsMem name) =
      add1RhsMem name (heuristicCountMapToNative counts) := by
  rw [WordHeuristicCountMap.addRhsMem, heuristicCountMap_update]
  unfold add1RhsMem
  rw [heuristicCountMap_lookup]
  cases found : counts.lookup name <;> simp [heuristicCountsToNative, wordHeuristicZero]

theorem heuristicCountMap_initial :
    heuristicCountMapToNative ({ entries := ∅ } : WordHeuristicCountMap) = .ln := rfl

private theorem unitInsertFold (names : List Nat) :
    RegAlloc.productionNumSetToNative
      (names.foldr (fun key tree => NumSet.insert key tree) .empty) =
      stackNamesTree names := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
      simp only [List.foldr_cons, RegAlloc.numSetInsert_production, ih,
        stackNamesTree, List.map_cons, sptFromAList]

private theorem canonicalKeys (names : List Nat) :
    NumSet.fromDistinctList names = (sptToAList (stackNamesTree names)).map Prod.fst := by
  have enumeration := RegAlloc.numSetToAList_production
    (names.foldr (fun key tree => NumSet.insert key tree) .empty) 0 []
  simp only [List.map_nil, unitInsertFold] at enumeration
  change sptToAList (stackNamesTree names) =
    (NumSet.fromDistinctList names).map (fun key => (key, ())) at enumeration
  have keys := congrArg (List.map Prod.fst) enumeration
  simpa only [List.map_map, Function.comp_def, List.map_id'] using keys.symm

private theorem toAListMapAux {α β : Type} (f : α → β) (tree : Spt α)
    (index : Nat) (accumulator : List (Nat × α)) :
    sptFoldi (fun key value accumulated => (key, value) :: accumulated) index
      (accumulator.map (fun entry => (entry.1, f entry.2))) (sptMap f tree) =
      (sptFoldi (fun key value accumulated => (key, value) :: accumulated)
        index accumulator tree).map (fun entry => (entry.1, f entry.2)) := by
  induction tree generalizing index accumulator with
  | ln => rfl
  | ls value => rfl
  | bn left right ihLeft ihRight =>
      simp only [sptMap, sptFoldi, ihLeft, ihRight]
  | bs left value right ihLeft ihRight =>
      simp only [sptMap, sptFoldi, ihLeft]
      simpa only [List.map_cons] using ihRight (index + lrNext index)
        ((index, value) :: sptFoldi (fun key value accumulated =>
          (key, value) :: accumulated) (index + 2 * lrNext index) accumulator left)

private theorem toAListMap {α β : Type} (f : α → β) (tree : Spt α) :
    sptToAList (sptMap f tree) =
      (sptToAList tree).map (fun entry => (entry.1, f entry.2)) :=
  toAListMapAux f tree 0 []

private theorem unitProjection (counts : WordHeuristicCountMap) :
    stackNamesTree counts.entries.keys =
      sptMap (fun _ => ()) (heuristicCountMapToNative counts) := by
  apply (sptEqThm _ _ ⟨sptWfFromAList _,
    by rw [sptWfMap]; exact heuristicCountMap_wf _⟩).mpr
  intro key
  rw [stackNamesTree_lookup, sptLookup_sptMap, heuristicCountMap_lookup]
  simp only [Std.TreeMap.mem_keys, Std.TreeMap.mem_iff_isSome_getElem?,
    WordHeuristicCountMap.lookup]
  cases counts.entries[key]? <;> rfl

/-- The actual key producer retains the original Patricia traversal order. -/
theorem heuristicCountMap_keys (counts : WordHeuristicCountMap) :
    counts.keys = (sptToAList (heuristicCountMapToNative counts)).map Prod.fst := by
  rw [WordHeuristicCountMap.keys, canonicalKeys, unitProjection, toAListMap]
  simp only [List.map_map, Function.comp_def]

private theorem renderEntries {α : Type} (entries : List (Nat × α))
    (lookup : Nat → Option α)
    (correct : ∀ entry ∈ entries, lookup entry.1 = some entry.2) :
    (entries.map Prod.fst).filterMap (fun key =>
      (lookup key).map (fun value => (key, value))) = entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      have head := correct entry (by simp)
      have tail : ∀ entry ∈ rest, lookup entry.1 = some entry.2 := by
        intro entry member
        exact correct entry (List.mem_cons_of_mem _ member)
      rcases entry with ⟨key, value⟩
      simp only [List.map_cons, List.filterMap_cons, head, Option.map_some,
        ih tail]

/-- Exact ordered production association list, including every five-counter
payload. This is stronger than lookup compatibility and preserves the
observable Patricia enumeration used by spill-cost and call-name producers. -/
theorem heuristicCountMap_render (counts : WordHeuristicCountMap) :
    counts.toNatInfoMap.map (fun entry => (entry.1, heuristicCountsToNative entry.2)) =
      sptToAList (heuristicCountMapToNative counts) := by
  unfold WordHeuristicCountMap.toNatInfoMap
  rw [List.map_filterMap]
  change counts.keys.filterMap _ = _
  have operation : (fun key =>
      Option.map (fun entry => (entry.1, heuristicCountsToNative entry.2))
        (match counts.entries[key]? with
        | some value => some (key, value)
        | none => none)) =
      (fun key => (sptLookup key (heuristicCountMapToNative counts)).map
        (fun value => (key, value))) := by
    funext key
    rw [heuristicCountMap_lookup]
    unfold WordHeuristicCountMap.lookup
    cases counts.entries[key]? <;> rfl
  apply (congrArg (fun operation : Nat → Option (Nat × HeuData) =>
    counts.keys.filterMap operation) operation).trans
  rw [heuristicCountMap_keys]
  apply renderEntries
  intro entry member
  rcases entry with ⟨key, value⟩
  exact (sptMemToAList _ _ _).mp member

end Flapjack.WordAlloc

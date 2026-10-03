import Flapjack.Compiler.Backend.WordAlloc.ProductionHeuristicProgram
import Flapjack.Compiler.Backend.WordAlloc.GetHeuristics

namespace Flapjack.WordAlloc
open RiscV

/-! Whole executed heuristic output correspondence. The native getHeuristics
definition already carries its reviewed HOL reference; these implementation
theorems derive the actual input collectors and cost map, including the
call-absence multiplier and both algorithm parities. -/

private theorem indexedAssocMap {α β : Type} (f : Nat → α → β)
    (entries : List (Nat × α)) (key : Nat) :
    sptAListLookup key (entries.map (fun entry => (entry.1, f entry.1 entry.2))) =
      (sptAListLookup key entries).map (f key) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, value⟩
      by_cases same : key = name <;> simp [sptAListLookup, same, ih]

theorem heuristicSpillState_production (counts : WordHeuristicCountMap)
    (calls : WordHeuristicCallSet) (valid : StackCacheRep calls.names calls.seen) :
    sptFromAList (counts.toNatInfoMap.map (fun entry =>
      (entry.1, wordGetSpillCost entry.2 (!calls.seen.contains entry.1)))) =
      sptMapi (fun key value =>
        getSpillCost value (sptLookup key (stackNamesTree calls.names)).isNone)
        (heuristicCountMapToNative counts) := by
  have absence (key : Nat) : (!calls.seen.contains key) =
      (sptLookup key (stackNamesTree calls.names)).isNone := by
    rw [stackCache_contains valid, stackNamesTree_lookup]
    by_cases member : key ∈ calls.names <;> simp [member]
  have rendered : counts.toNatInfoMap.map (fun entry =>
      (entry.1, wordGetSpillCost entry.2 (!calls.seen.contains entry.1))) =
      (sptToAList (heuristicCountMapToNative counts)).map (fun entry =>
        (entry.1, getSpillCost entry.2
          (sptLookup entry.1 (stackNamesTree calls.names)).isNone)) := by
    rw [← heuristicCountMap_render, List.map_map]
    apply List.map_congr_left
    intro entry _
    simp only [Function.comp_def, spillCost_production, absence]
  rw [rendered]
  apply (sptEqThm _ _ ⟨sptWfFromAList _, sptWfMapi _ _⟩).mpr
  intro key
  rw [sptLookup_sptFromAList,
    indexedAssocMap (fun name value => getSpillCost value
      (sptLookup name (stackNamesTree calls.names)).isNone) _ key, sptLookupMapi]
  have original := sptLookup_sptFromAList_sptToAList key (heuristicCountMapToNative counts)
  rw [sptLookup_sptFromAList] at original
  rw [original]

theorem heuristicSpillCosts_production {width : Nat} [NeZero width]
    (functionName : Nat) (program : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    sptFromAList (wordHeuristicSpillCostsFast functionName program) =
      (let result := getHeu functionName native (.ln, .ln)
       sptMapi (fun key value => getSpillCost value (sptLookup key result.2).isNone)
         result.1) := by
  rw [← heuristicProgram_initial functionName program native encoded]
  exact heuristicSpillState_production _ _
    (heuristicCache_preserved functionName program {} {} callCache_initial)

theorem getHeuristics_production {width : Nat} [NeZero width]
    (algorithm functionName : Nat) (program : WordProg (BitVec width))
    (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native) :
    ((wordGetHeuristics algorithm functionName program).1.map wordMoveToTriple,
      (wordGetHeuristics algorithm functionName program).2.map sptFromAList) =
      getHeuristics algorithm functionName native := by
  simp only [wordGetHeuristics, getHeuristics]
  split
  · simp only [weightedPreferences_production program native encoded,
      heuristicSpillCosts_production functionName program native encoded, Option.map_some]
  · have prefs := preferences_production program native encoded []
    simpa only [List.append_nil, Option.map_none] using congrArg (fun moves => (moves, none)) prefs

end Flapjack.WordAlloc

import Flapjack.Compiler.Backend.WordAlloc.ProductionPreferences
import Flapjack.Compiler.Backend.WordAlloc.CoalesceCost
import Flapjack.Compiler.Backend.WordAlloc.Heuristics
import Flapjack.Compiler.Backend.WordAlloc.ProductionStackOnlyCache
import Flapjack.Compiler.Backend.WordAlloc.HeuCounters

namespace Flapjack.WordAlloc
open RiscV

/-! Actual accelerated heuristic output arithmetic. Untagged implementation
correspondence to the already reviewed native definitions. Presence of an
endpoint is derived from the actual spill-cost associations, including
repeated keys and zero costs; no membership equivalence is assumed. -/

abbrev heuristicCountsToNative (counts : WordHeuristicCounts) : HeuData :=
  (counts.lhsConst, counts.lhsReg, counts.lhsMem, counts.rhsReg, counts.rhsMem)

theorem spillCost_production (counts : WordHeuristicCounts) (tail : Bool) :
    wordGetSpillCost counts tail = getSpillCost (heuristicCountsToNative counts) tail := rfl

private theorem keysFold_member (entries : NatInfoMap Nat) (seen : Std.TreeSet Nat) (key : Nat) :
    key ∈ entries.foldl (fun seen entry => seen.insert entry.1) seen ↔
      key ∈ entries.map Prod.fst ∨ key ∈ seen := by
  induction entries generalizing seen with
  | nil => simp
  | cons head rest ih =>
      simp only [List.foldl_cons, ih, Std.TreeSet.mem_insert,
        Std.LawfulEqCmp.compare_eq_iff_eq, List.map_cons, List.mem_cons]
      simp only [or_assoc, or_left_comm, eq_comm]

private theorem lookupPresence (entries : NatInfoMap Nat) (key : Nat) :
    (sptAListLookup key entries).isSome = decide (key ∈ entries.map Prod.fst) := by
  induction entries with
  | nil => rfl
  | cons head rest ih =>
      rcases head with ⟨name, value⟩
      by_cases same : key = name <;> simp [sptAListLookup, same, ih]

theorem spillCostKeys_production (entries : NatInfoMap Nat) (key : Nat) :
    (wordSpillCostKeys entries).contains key = (sptLookup key (sptFromAList entries)).isSome := by
  rw [sptLookup_sptFromAList, lookupPresence]
  apply stackCache_contains
  intro other
  have empty : other ∉ (∅ : Std.TreeSet Nat) := Std.TreeSet.not_mem_emptyc
  constructor
  · intro found
    unfold wordSpillCostKeys at found
    rcases (keysFold_member entries (∅ : Std.TreeSet Nat) other).mp found with member | absent
    · exact member
    · exact False.elim (empty absent)
  · intro member
    exact (keysFold_member entries (∅ : Std.TreeSet Nat) other).mpr (Or.inl member)

theorem coalesceCost_production (entries : NatInfoMap Nat) (move : WordCanonicalMove) :
    wordMoveToTriple (wordCoalesceMoveCostFast (wordSpillCostKeys entries) move) =
      getCoalesceCost (sptFromAList entries)
        (move.count, move.maxPriority, (move.left, move.right)) := by
  simp only [wordCoalesceMoveCostFast, wordMoveToTriple, getCoalesceCost, spillCostKeys_production]
  cases sptLookup move.left (sptFromAList entries) <;>
    cases sptLookup move.right (sptFromAList entries) <;> rfl

theorem coalesceCosts_production (entries : NatInfoMap Nat) (moves : List WordCanonicalMove) :
    (wordCoalesceMoveCostsFast entries moves).map wordMoveToTriple =
      (moves.map (fun move => (move.count, move.maxPriority, (move.left, move.right)))).map
        (getCoalesceCost (sptFromAList entries)) := by
  simp only [wordCoalesceMoveCostsFast, List.map_map]
  apply List.map_congr_left
  intro move _
  exact coalesceCost_production entries move

/-- Actual priority collection, canonicalization and accelerated cost weighting
compose to the complete native preference pipeline on accepted source programs.
The spill map is an arbitrary input; proving its actual counter producer remains
a separate dependency, rather than assuming the full heuristic output. -/
theorem weightedPreferences_production {width : Nat} [NeZero width]
    (program : WordProg (BitVec width)) (native : WordLangProgHOL (BitVec width))
    (encoded : wordLangProgToHOL program = some native)
    (entries : NatInfoMap Nat) :
    (wordCoalesceMoveCostsFast entries
      (wordCanonicalizeMoves (wordProgPrioritizedMoves program))).map wordMoveToTriple =
      (canonizeMoves (getPrefs native [])).map (getCoalesceCost (sptFromAList entries)) := by
  rw [coalesceCosts_production, canonicalPreferences_production program native encoded]

end Flapjack.WordAlloc

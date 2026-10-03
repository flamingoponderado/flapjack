import Flapjack.Compiler.Backend.WordAlloc.ProductionStackOnlyCache
import Flapjack.Compiler.Backend.WordAlloc.HeuCall
import Flapjack.RiscV.Heuristics

namespace Flapjack.WordAlloc
open RiscV

/-! The actual self-call cache and its duplicate scan. These implementation
invariants have no independent HOL original. Cache membership is derived
from the real updates, rather than assumed for a resulting call set. -/

theorem dedupAux_member (seen : Std.TreeSet Nat) (names : List Nat) (key : Nat) :
    key ∈ natEraseDupsAux seen names ↔ key ∈ names ∧ key ∉ seen := by
  induction names generalizing seen with
  | nil => simp [natEraseDupsAux]
  | cons name rest ih =>
      by_cases present : name ∈ seen
      · have contains := Std.TreeSet.contains_iff_mem.mpr present
        simp only [natEraseDupsAux, contains, if_true, ih, List.mem_cons]
        constructor
        · intro h; exact ⟨Or.inr h.1, h.2⟩
        · rintro ⟨equal | member, missing⟩
          · exact False.elim (missing (equal ▸ present))
          · exact ⟨member, missing⟩
      · have contains : seen.contains name = false :=
          Bool.eq_false_iff.mpr (fun h => present (Std.TreeSet.contains_iff_mem.mp h))
        simp only [natEraseDupsAux, contains, Bool.false_eq_true, if_false,
          List.mem_cons, ih, Std.TreeSet.mem_insert,
          Std.LawfulEqCmp.compare_eq_iff_eq]
        by_cases same : key = name <;> simp [same, present, eq_comm]

theorem dedupAux_nodup (seen : Std.TreeSet Nat) (names : List Nat) :
    (natEraseDupsAux seen names).Nodup := by
  induction names generalizing seen with
  | nil => simp [natEraseDupsAux]
  | cons name rest ih =>
      unfold natEraseDupsAux
      split
      · exact ih seen
      · apply List.nodup_cons.mpr
        refine ⟨?_, ih _⟩
        rw [dedupAux_member]
        simp

theorem dedupAppendAux_eq (seen : Std.TreeSet Nat) (left right : List Nat) :
    natEraseDupsAppendAux seen left right = natEraseDupsAux seen (left ++ right) := by
  induction left generalizing seen with
  | nil => simp [natEraseDupsAppendAux]
  | cons name rest ih =>
      simp only [natEraseDupsAppendAux, List.cons_append, natEraseDupsAux]
      split <;> simp only [ih]

theorem dedupAppend_member (left right : List Nat) (key : Nat) :
    key ∈ natEraseDupsAppend left right ↔ key ∈ left ∨ key ∈ right := by
  rw [natEraseDupsAppend, dedupAppendAux_eq, dedupAux_member]
  simp

theorem dedupAppend_nodup (left right : List Nat) :
    (natEraseDupsAppend left right).Nodup := by
  rw [natEraseDupsAppend, dedupAppendAux_eq]
  exact dedupAux_nodup _ _

theorem callMergeFast_production (left right : List Nat) :
    stackNamesTree (wordHeuristicMergeCallsFast left right) =
      heuMergeCall (stackNamesTree left) (stackNamesTree right) := by
  have canonical : wordHeuristicMergeCallsFast left right =
      NumSet.fromList (natEraseDupsAppend left right) :=
    NumSet.fromDistinctList_eq (dedupAppend_nodup left right)
  rw [canonical]
  unfold stackNamesTree
  rw [numSetFromList_production]
  change stackNamesTree (natEraseDupsAppend left right) = _
  apply (sptEqThm _ _ ⟨sptWfFromAList _,
    sptWfUnion _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩⟩).mpr
  intro key
  simp only [sptLookup_sptUnion, stackNamesTree_lookup, dedupAppend_member]
  by_cases l : key ∈ left <;> by_cases r : key ∈ right <;> simp [l, r]

private theorem callFold_member (right : List Nat) (calls : WordHeuristicCallSet)
    (key : Nat) :
    key ∈ (right.foldl (fun calls name =>
      if calls.seen.contains name then calls
      else { names := name :: calls.names, seen := calls.seen.insert name }) calls).seen ↔
      key ∈ right ∨ key ∈ calls.seen := by
  induction right generalizing calls with
  | nil => simp
  | cons name rest ih =>
      simp only [List.foldl_cons, ih, List.mem_cons]
      by_cases present : name ∈ calls.seen
      · have contains := Std.TreeSet.contains_iff_mem.mpr present
        simp only [contains, if_true]
        by_cases same : key = name <;> simp [same, present]
      · have contains : calls.seen.contains name = false :=
          Bool.eq_false_iff.mpr (fun h => present (Std.TreeSet.contains_iff_mem.mp h))
        simp only [contains, Bool.false_eq_true, if_false, Std.TreeSet.mem_insert,
          Std.LawfulEqCmp.compare_eq_iff_eq]
        simp only [or_assoc, or_left_comm, eq_comm]

/-- The actual cache merge preserves membership and produces the native union.
The input cache invariant is satisfied by the real empty initial call set. -/
theorem callCache_merge (calls : WordHeuristicCallSet) (right : List Nat)
    (valid : StackCacheRep calls.names calls.seen) :
    stackNamesTree (calls.merge right).names =
        heuMergeCall (stackNamesTree calls.names) (stackNamesTree right) ∧
      StackCacheRep (calls.merge right).names (calls.merge right).seen := by
  refine ⟨callMergeFast_production _ _, ?_⟩
  intro key
  have native := callMergeFast_production calls.names right
  have lookups := congrArg (sptLookup key) native
  simp only [heuMergeCall, sptLookup_sptUnion, stackNamesTree_lookup] at lookups
  have membership : key ∈ wordHeuristicMergeCallsFast calls.names right ↔
      key ∈ calls.names ∨ key ∈ right := by
    by_cases l : key ∈ calls.names <;> by_cases r : key ∈ right <;>
      by_cases result : key ∈ wordHeuristicMergeCallsFast calls.names right <;>
      simp_all
  simp only [WordHeuristicCallSet.merge, callFold_member, valid key, membership]
  exact or_comm

theorem callCache_initial : StackCacheRep
    ({ names := [], seen := ∅ } : WordHeuristicCallSet).names ({ names := [], seen := ∅ } : WordHeuristicCallSet).seen := by
  intro key
  simp

end Flapjack.WordAlloc

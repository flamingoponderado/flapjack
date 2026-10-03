import Flapjack.Compiler.Backend.RegAlloc.ProductionInitTags
import Flapjack.Compiler.Backend.WordAlloc.ProductionCutsetContext
import Flapjack.Misc.SptreeLookup
import Flapjack.Compiler.Backend.WordAlloc.StackOnly
import Flapjack.Compiler.Backend.WordAlloc.MergeStackSets

namespace Flapjack.WordAlloc
open RiscV

/-! Actual list-set operations used by the stack-only analysis, transported to
native unit trees. These are implementation correspondence lemmas, with no
independent HOL original. Deletion deliberately requires distinct names:
production List.erase removes only one occurrence, whereas native deletion
removes the key. The complete producer must derive this invariant from its
empty initial state. -/

abbrev stackNamesTree (names : List Nat) : Spt Unit :=
  sptFromAList (names.map (fun name => (name, ())))

theorem stackNamesTree_lookup (names : List Nat) (key : Nat) :
    sptLookup key (stackNamesTree names) = if key ∈ names then some () else none := by
  rw [sptLookup_sptFromAList]
  induction names with
  | nil => rfl
  | cons name rest ih => by_cases equal : key = name <;> simp [sptAListLookup, ih, equal]

private theorem cachedMembership (names : List Nat) (key : Nat) :
    (natSetOfList names).contains key = decide (key ∈ names) := by
  rw [RegAlloc.stackOnlyCodec_production, stackNamesTree_lookup]
  split <;> simp_all

private theorem treesEqual (names : List Nat) (tree : Spt Unit)
    (wf : sptWf tree = true)
    (lookups : ∀ key, sptLookup key (stackNamesTree names) = sptLookup key tree) :
    stackNamesTree names = tree :=
  (sptEqThm _ _ ⟨sptWfFromAList _, wf⟩).mpr lookups

theorem stackInsert_production (key : Nat) (names : List Nat) :
    stackNamesTree (CakeAlloc.insertSet key names) = sptInsert key () (stackNamesTree names) := by
  apply treesEqual _ _ (sptWfInsert _ _ _ (sptWfFromAList _))
  intro other
  unfold CakeAlloc.insertSet
  by_cases same : other = key
  · subst other
    rw [sptLookup_sptInsert_same]
    by_cases member : key ∈ names <;> simp [member, stackNamesTree_lookup]
  · rw [sptLookup_sptInsert_ne key other () _ same]
    by_cases member : key ∈ names <;> simp [member, stackNamesTree_lookup, same]

theorem stackDelete_production (key : Nat) (names : List Nat) (unique : names.Nodup) :
    stackNamesTree (CakeAlloc.deleteSet key names) = sptDelete key (stackNamesTree names) := by
  apply treesEqual _ _ (sptWfDelete _ _ (sptWfFromAList _))
  intro other
  rw [sptLookup_sptDelete]
  simp only [CakeAlloc.deleteSet, stackNamesTree_lookup, unique.mem_erase_iff]
  by_cases same : other = key <;> simp [same]

theorem stackUnion_production (left right : List Nat) :
    stackNamesTree (CakeAlloc.unionSet left right) = sptUnion (stackNamesTree left) (stackNamesTree right) := by
  apply treesEqual _ _ (sptWfUnion _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩)
  intro key
  rw [sptLookup_sptUnion]
  simp only [stackNamesTree_lookup, CakeAlloc.unionSet, List.mem_append,
    List.mem_filter, cachedMembership]
  by_cases l : key ∈ left <;> by_cases r : key ∈ right <;> simp [l, r]

theorem stackInter_production (left right : List Nat) :
    stackNamesTree (CakeAlloc.interSet left right) = sptInter (stackNamesTree left) (stackNamesTree right) := by
  apply treesEqual _ _ (sptWfInter _ _)
  intro key
  rw [sptLookup_sptInterCases]
  simp only [stackNamesTree_lookup, CakeAlloc.interSet, List.mem_filter, cachedMembership]
  by_cases l : key ∈ left <;> by_cases r : key ∈ right <;> simp [l, r]

theorem stackDiff_production (left right : List Nat) :
    stackNamesTree (CakeAlloc.diffSet left right) = sptDifference (stackNamesTree left) (stackNamesTree right) := by
  apply treesEqual _ _ (sptWfDifference _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩)
  intro key
  rw [sptLookupDifference]
  simp only [stackNamesTree_lookup, CakeAlloc.diffSet, List.mem_filter, cachedMembership]
  by_cases l : key ∈ left <;> by_cases r : key ∈ right <;> simp [l, r]

theorem stackInsert_nodup (key : Nat) (names : List Nat) (unique : names.Nodup) :
    (CakeAlloc.insertSet key names).Nodup := by
  unfold CakeAlloc.insertSet
  by_cases member : key ∈ names <;> simp [member, unique]

theorem stackDelete_nodup (key : Nat) (names : List Nat) (unique : names.Nodup) :
    (CakeAlloc.deleteSet key names).Nodup := unique.erase key

theorem stackUnion_nodup (left right : List Nat) (hl : left.Nodup) (hr : right.Nodup) :
    (CakeAlloc.unionSet left right).Nodup := by
  unfold CakeAlloc.unionSet
  apply List.nodup_append.mpr
  refine ⟨hl, hr.filter _, ?_⟩
  intro a ha b hb equal
  subst b
  have missing := (List.mem_filter.mp hb).2
  simp [cachedMembership, ha] at missing

theorem stackInter_nodup (left right : List Nat) (unique : left.Nodup) :
    (CakeAlloc.interSet left right).Nodup := unique.filter _

theorem stackDiff_nodup (left right : List Nat) (unique : left.Nodup) :
    (CakeAlloc.diffSet left right).Nodup := unique.filter _


abbrev stackPairTree (pair : List Nat × List Nat) : Spt Unit × Spt Unit :=
  (stackNamesTree pair.1, stackNamesTree pair.2)

theorem stackMove_production (x y : Nat) (temporary fixed : List Nat)
    (unique : temporary.Nodup) :
    stackPairTree (CakeAlloc.mergeStackOnly x y temporary fixed) =
      mergeStackOnly (x, y) (stackNamesTree temporary, stackNamesTree fixed) := by
  by_cases member : x ∈ temporary <;>
    by_cases alloc : y % 4 = 1 <;>
    by_cases physical : y % 2 = 0 <;>
    by_cases stack : x % 4 = 3 <;>
    simp [CakeAlloc.mergeStackOnly, mergeStackOnly, stackPairTree,
      stackNamesTree_lookup, member, alloc, physical, stack, CakeAlloc.isAllocVar,
      CakeAlloc.isPhyVar, CakeAlloc.isStackVar, isAllocVar, isPhyVar, isStackVar,
      stackInsert_production, stackDelete_production, unique]

theorem stackMove_nodup (x y : Nat) (temporary fixed : List Nat)
    (ht : temporary.Nodup) (hf : fixed.Nodup) :
    (CakeAlloc.mergeStackOnly x y temporary fixed).1.Nodup ∧
      (CakeAlloc.mergeStackOnly x y temporary fixed).2.Nodup := by
  unfold CakeAlloc.mergeStackOnly
  split
  · split <;> split <;> simp [stackInsert_nodup, ht, hf]
  · split
    · split <;> simp [stackInsert_nodup, ht, hf]
    · exact ⟨stackDelete_nodup _ _ ht, hf⟩

theorem stackMerge_production (initial left right : List Nat × List Nat) :
    stackPairTree (CakeAlloc.mergeStackSets initial.1 initial.2 left.1 left.2 right.1 right.2) =
      mergeStackSets (stackPairTree initial) (stackPairTree left) (stackPairTree right) := by
  simp only [CakeAlloc.mergeStackSets, mergeStackSets, stackPairTree,
    stackUnion_production, stackInter_production, stackDiff_production]

theorem stackMerge_nodup (initial left right : List Nat × List Nat)
    (hl : left.1.Nodup ∧ left.2.Nodup) (hr : right.1.Nodup ∧ right.2.Nodup) :
    (CakeAlloc.mergeStackSets initial.1 initial.2 left.1 left.2 right.1 right.2).1.Nodup ∧
      (CakeAlloc.mergeStackSets initial.1 initial.2 left.1 left.2 right.1 right.2).2.Nodup := by
  exact ⟨stackUnion_nodup _ _ (stackInter_nodup _ _ hr.1)
    (stackUnion_nodup _ _ (stackDiff_nodup _ _ hl.1) (stackDiff_nodup _ _ hr.1)),
    stackUnion_nodup _ _ hl.2 hr.2⟩


private theorem deleteFold_nodup (keys names : List Nat) (unique : names.Nodup) :
    (keys.foldr CakeAlloc.deleteSet names).Nodup := by
  induction keys with
  | nil => exact unique
  | cons key keys ih => exact stackDelete_nodup _ _ ih

theorem stackRemove_production (keys temporary fixed : List Nat) (unique : temporary.Nodup) :
    stackPairTree (CakeAlloc.removeTempStack keys temporary fixed) =
      removeTempStack keys (stackNamesTree temporary, stackNamesTree fixed) := by
  have same : stackNamesTree (keys.foldr CakeAlloc.deleteSet temporary) =
      keys.foldr sptDelete (stackNamesTree temporary) := by
    induction keys with
    | nil => rfl
    | cons key keys ih =>
        rw [List.foldr_cons, stackDelete_production _ _ (deleteFold_nodup _ _ unique), ih]
        rfl
  exact congrArg (fun tree => (tree, stackNamesTree fixed)) same

theorem stackRemove_nodup (keys temporary fixed : List Nat)
    (ht : temporary.Nodup) (hf : fixed.Nodup) :
    (CakeAlloc.removeTempStack keys temporary fixed).1.Nodup ∧
      (CakeAlloc.removeTempStack keys temporary fixed).2.Nodup :=
  ⟨deleteFold_nodup _ _ ht, hf⟩

end Flapjack.WordAlloc

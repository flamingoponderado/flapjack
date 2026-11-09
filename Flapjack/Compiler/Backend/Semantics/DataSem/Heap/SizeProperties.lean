module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Heap
public import Flapjack.Misc.Sptree.Subspt
public import Flapjack.Misc.SptreeLookup

@[expose] public section

/-! Reference-tree bounds for source heap size accounting. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack

/-- Flapjack infrastructure: source heap sizing never increases the size of
the remaining reference tree. -/
theorem sizeOfValues_refsBound (limits : Limits) (values : List Value)
    (refs : Spt (BvlSem.Ref Value)) (seen : Spt Unit) :
    sptSize (sizeOfValues limits values refs seen).2.1 ≤ sptSize refs := by
  cases values with
  | nil => simp [sizeOfValues]
  | cons x xs =>
    cases xs with
    | cons y ys =>
      let first := checkRes refs (sizeOfValues limits (y :: ys) refs seen)
      have firstBound : sptSize first.2.1 ≤ sptSize refs := by
        dsimp [first, checkRes]
        split <;> simp_all
      have next := sizeOfValues_refsBound limits [x] first.2.1 first.2.2
      simpa only [sizeOfValues] using Nat.le_trans next firstBound
    | nil =>
      cases x with
      | number n => simp [sizeOfValues]
      | word64 w => simp [sizeOfValues]
      | codePtr n => simp [sizeOfValues]
      | refPtr bit address =>
        rw [sizeOfValues]
        split
        · simp
        · rename_i mode bytes found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          exact Nat.le_of_lt smaller
        · rename_i vals found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          have next := sizeOfValues_refsBound limits vals (sptDelete address refs) seen
          cases result : sizeOfValues limits vals (sptDelete address refs) seen with
          | mk n tail => cases tail; simpa [result] using Nat.le_trans next (Nat.le_of_lt smaller)
        · rename_i mode value found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          have next := sizeOfValues_refsBound limits [value] (sptDelete address refs) seen
          cases result : sizeOfValues limits [value] (sptDelete address refs) seen with
          | mk n tail => cases tail; simpa [result] using Nat.le_trans next (Nat.le_of_lt smaller)
        · rename_i tag final left value right found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          have next := sizeOfValues_refsBound limits (left ++ [value] ++ right) (sptDelete address refs) seen
          cases result : sizeOfValues limits (left ++ [value] ++ right) (sptDelete address refs) seen with
          | mk n tail =>
            cases tail
            rw [result] at next
            simpa using Nat.le_trans next (Nat.le_of_lt smaller)
      | block timestamp tag vals =>
        cases vals with
        | nil => simp [sizeOfValues]
        | cons value rest =>
          by_cases visited : (sptLookup timestamp seen).isSome = true
          · simp [sizeOfValues, visited]
          · have next := sizeOfValues_refsBound limits (value :: rest) refs (sptInsert timestamp () seen)
            simpa [sizeOfValues, visited] using next
termination_by (sptSize refs, sizeOf values)
decreasing_by
  all_goals simp_wf
  all_goals try (apply Prod.Lex.right; omega)
  all_goals try (apply Prod.Lex.left; exact smaller)
  have hy : 0 < sizeOf y := by cases y <;> simp_wf <;> omega
  dsimp only [first] at firstBound
  omega

/-- The growth guard is redundant for a result produced by heap sizing. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "check_res_size_of"]
theorem checkRes_sizeOfValues (limits : Limits) (values : List Value)
    (refs : Spt (BvlSem.Ref Value)) (seen : Spt Unit) :
    checkRes refs (sizeOfValues limits values refs seen) = sizeOfValues limits values refs seen := by
  simp [checkRes, sizeOfValues_refsBound]

/-- Flapjack infrastructure: deleting an entry preserves all remaining
key/value bindings of a sparse tree. -/
theorem sptDelete_subspt {α : Type} (tree : Spt α) (key : Nat) :
    sptSubspt (sptDelete key tree) tree := by
  apply (sptSubsptLookup _ _).mpr
  intro other value found
  rw [sptLookup_sptDelete] at found
  split at found
  · simp at found
  · exact found

/-- Flapjack infrastructure: source sizing only removes reference bindings;
every reference left in the result is unchanged from the input tree. -/
theorem sizeOfValues_refsSubspt (limits : Limits) (values : List Value)
    (refs : Spt (BvlSem.Ref Value)) (seen : Spt Unit) :
    sptSubspt (sizeOfValues limits values refs seen).2.1 refs := by
  cases values with
  | nil => simp [sizeOfValues, sptSubsptLookup]
  | cons x xs =>
    cases xs with
    | cons y ys =>
      let first := sizeOfValues limits (y :: ys) refs seen
      have firstBound : sptSize first.2.1 ≤ sptSize refs := sizeOfValues_refsBound limits (y :: ys) refs seen
      have firstSub := sizeOfValues_refsSubspt limits (y :: ys) refs seen
      have next := sizeOfValues_refsSubspt limits [x] first.2.1 first.2.2
      have together := sptSubsptTrans _ _ _ ⟨next, firstSub⟩
      simpa only [sizeOfValues, checkRes_sizeOfValues] using together
    | nil =>
      cases x with
      | number n => simp [sizeOfValues, sptSubsptLookup]
      | word64 w => simp [sizeOfValues, sptSubsptLookup]
      | codePtr n => simp [sizeOfValues, sptSubsptLookup]
      | refPtr bit address =>
        rw [sizeOfValues]
        split
        · simp [sptSubsptLookup]
        · exact sptDelete_subspt refs address
        · rename_i vals found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          have next := sizeOfValues_refsSubspt limits vals (sptDelete address refs) seen
          have resultSub := sptSubsptTrans _ _ _ ⟨next, sptDelete_subspt refs address⟩
          cases result : sizeOfValues limits vals (sptDelete address refs) seen with
          | mk n tail => cases tail; simpa [result] using resultSub
        · rename_i mode value found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          have next := sizeOfValues_refsSubspt limits [value] (sptDelete address refs) seen
          have resultSub := sptSubsptTrans _ _ _ ⟨next, sptDelete_subspt refs address⟩
          cases result : sizeOfValues limits [value] (sptDelete address refs) seen with
          | mk n tail => cases tail; simpa [result] using resultSub
        · rename_i tag final left value right found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          have next := sizeOfValues_refsSubspt limits (left ++ [value] ++ right) (sptDelete address refs) seen
          have resultSub := sptSubsptTrans _ _ _ ⟨next, sptDelete_subspt refs address⟩
          cases result : sizeOfValues limits (left ++ [value] ++ right) (sptDelete address refs) seen with
          | mk n tail =>
            cases tail
            rw [result] at resultSub
            simpa using resultSub
      | block timestamp tag vals =>
        cases vals with
        | nil => simp [sizeOfValues, sptSubsptLookup]
        | cons value rest =>
          by_cases visited : (sptLookup timestamp seen).isSome = true
          · simp [sizeOfValues, visited, sptSubsptLookup]
          · have next := sizeOfValues_refsSubspt limits (value :: rest) refs (sptInsert timestamp () seen)
            simpa [sizeOfValues, visited] using next
termination_by (sptSize refs, sizeOf values)
decreasing_by
  all_goals simp_wf
  all_goals try (apply Prod.Lex.right; omega)
  all_goals try (apply Prod.Lex.left; exact smaller)
  have hy : 0 < sizeOf y := by cases y <;> simp_wf <;> omega
  dsimp only [first] at firstBound
  omega

/-- Flapjack infrastructure: inserting a visited timestamp preserves the
bindings already present in the unit-valued seen tree. -/
theorem sptUnit_insert_superset (tree : Spt Unit) (key : Nat) :
    sptSubspt tree (sptInsert key () tree) := by
  apply (sptSubsptLookup _ _).mpr
  intro other value found
  cases value
  by_cases equal : other = key
  · subst other
    exact sptLookup_sptInsert_same key () tree
  · simpa [sptLookup_sptInsert_ne key other () tree equal] using found

/-- Flapjack infrastructure: source sizing never discards an already seen
block timestamp. -/
theorem sizeOfValues_seenSubspt (limits : Limits) (values : List Value)
    (refs : Spt (BvlSem.Ref Value)) (seen : Spt Unit) :
    sptSubspt seen (sizeOfValues limits values refs seen).2.2 := by
  cases values with
  | nil => simp [sizeOfValues, sptSubsptLookup]
  | cons x xs =>
    cases xs with
    | cons y ys =>
      let first := sizeOfValues limits (y :: ys) refs seen
      have firstBound : sptSize first.2.1 ≤ sptSize refs := sizeOfValues_refsBound limits (y :: ys) refs seen
      have firstSub := sizeOfValues_seenSubspt limits (y :: ys) refs seen
      have next := sizeOfValues_seenSubspt limits [x] first.2.1 first.2.2
      have together := sptSubsptTrans _ _ _ ⟨firstSub, next⟩
      simpa only [sizeOfValues, checkRes_sizeOfValues] using together
    | nil =>
      cases x with
      | number n => simp [sizeOfValues, sptSubsptLookup]
      | word64 w => simp [sizeOfValues, sptSubsptLookup]
      | codePtr n => simp [sizeOfValues, sptSubsptLookup]
      | refPtr bit address =>
        rw [sizeOfValues]
        split
        · simp [sptSubsptLookup]
        · simp [sptSubsptLookup]
        · rename_i vals found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          have next := sizeOfValues_seenSubspt limits vals (sptDelete address refs) seen
          cases result : sizeOfValues limits vals (sptDelete address refs) seen with
          | mk n tail => cases tail; simpa [result] using next
        · rename_i mode value found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          have next := sizeOfValues_seenSubspt limits [value] (sptDelete address refs) seen
          cases result : sizeOfValues limits [value] (sptDelete address refs) seen with
          | mk n tail => cases tail; simpa [result] using next
        · rename_i tag final left value right found
          have smaller : sptSize (sptDelete address refs) < sptSize refs :=
            sptSize_delete_lt refs address (by rw [found]; simp)
          have next := sizeOfValues_seenSubspt limits (left ++ [value] ++ right) (sptDelete address refs) seen
          cases result : sizeOfValues limits (left ++ [value] ++ right) (sptDelete address refs) seen with
          | mk n tail =>
            cases tail
            rw [result] at next
            simpa using next
      | block timestamp tag vals =>
        cases vals with
        | nil => simp [sizeOfValues, sptSubsptLookup]
        | cons value rest =>
          by_cases visited : (sptLookup timestamp seen).isSome = true
          · simp [sizeOfValues, visited, sptSubsptLookup]
          · have next := sizeOfValues_seenSubspt limits (value :: rest) refs (sptInsert timestamp () seen)
            have together := sptSubsptTrans _ _ _ ⟨sptUnit_insert_superset seen timestamp, next⟩
            simpa [sizeOfValues, visited] using together
termination_by (sptSize refs, sizeOf values)
decreasing_by
  all_goals simp_wf
  all_goals try (apply Prod.Lex.right; omega)
  all_goals try (apply Prod.Lex.left; exact smaller)
  have hy : 0 < sizeOf y := by cases y <;> simp_wf <;> omega
  dsimp only [first] at firstBound
  omega

end Flapjack.Compiler.Backend.DataSem

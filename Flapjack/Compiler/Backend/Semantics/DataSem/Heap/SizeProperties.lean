import Flapjack.Compiler.Backend.Semantics.DataSem.Heap

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

end Flapjack.Compiler.Backend.DataSem

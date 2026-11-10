module

public import Flapjack.Compiler.Backend.ClosToBvl.Sort
public import Mathlib.Data.List.Permutation

@[expose] public section

namespace Flapjack.Compiler.Backend.ClosToBvl

@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "code_split_IMP_PERM"]
theorem codeSplit_imp_perm {α : Type} (xs1 xs2 xs3 ts1 ts2 : List α)
    (split : codeSplit xs1 xs2 xs3 = (ts1, ts2)) :
    (ts1 ++ ts2).Perm (xs2 ++ xs3 ++ xs1) := by
  classical
  rw [List.perm_iff_count]
  intro value
  induction xs1 generalizing xs2 xs3 with
  | nil =>
    simp [codeSplit] at split
    rcases split with ⟨rfl, rfl⟩
    simp
  | cons head tail ih =>
    have h := ih (head :: xs3) xs2 (by simpa [codeSplit] using split)
    simp only [List.count_append, List.count_cons] at h ⊢
    omega

private theorem merge_perm {α : Type} (xs ys : List (Nat × α)) :
    (codeMerge xs ys).Perm (xs ++ ys) := by
  cases xs with
  | nil => simp [codeMerge]
  | cons x xs =>
    cases ys with
    | nil => simp [codeMerge]
    | cons y ys =>
      simp only [codeMerge]
      split
      · exact (merge_perm xs (y :: ys)).cons x
      · exact ((merge_perm (x :: xs) ys).cons y).trans (by simpa using (List.perm_middle (l₁ := x :: xs) (l₂ := ys) (a := y)).symm)
termination_by xs.length + ys.length
decreasing_by all_goals simp_wf

/-- Merge preserves any permutation of its two inputs. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "IMP_PERM_code_merge"]
theorem codeMerge_imp_perm {α : Type} (xs ys zs : List (Nat × α))
    (h : (xs ++ ys).Perm zs) : (codeMerge xs ys).Perm zs :=
  (merge_perm xs ys).trans h

/-- Sorting preserves the complete list of code entries. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "PERM_code_sort"]
theorem codeSort_perm {α : Type} (xs : List (Nat × α)) : (codeSort xs).Perm xs := by
  fun_induction codeSort xs with
  | case1 => rfl
  | case2 => rfl
  | case3 x y rest left right =>
    refine (merge_perm _ _).trans ((left.append right).trans ?_)
    have split := codeSplit_imp_perm rest [x] [y] (codeSplit rest [x] [y]).1
      (codeSplit rest [x] [y]).2 (Prod.eta _).symm
    simpa using split

/-- Sorting preserves distinctness of code labels. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "ALL_DISTINCT_code_sort"]
theorem codeSort_allDistinct {α : Type} (xs : List (Nat × α)) :
    ((codeSort xs).map Prod.fst).Nodup ↔ (xs.map Prod.fst).Nodup := by
  exact ((codeSort_perm xs).map Prod.fst).nodup_iff


end Flapjack.Compiler.Backend.ClosToBvl

import Flapjack.HolRef

/-! The source's alternating split and merge sort for generated code. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Distribute the remaining entries between the two accumulators, swapping
the accumulator roles at each step exactly as in the source. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "code_split_def"]
def codeSplit {α : Type} : List α → List α → List α → List α × List α
  | [], xs, ys => (xs, ys)
  | z :: zs, xs, ys => codeSplit zs (z :: ys) xs

private theorem splitLength {α : Type} (ts xs ys : List α) :
    (codeSplit ts xs ys).1.length + (codeSplit ts xs ys).2.length =
      ts.length + xs.length + ys.length := by
  induction ts generalizing xs ys with
  | nil => simp [codeSplit]
  | cons z zs ih => simp only [codeSplit, List.length_cons, ih]; omega

private theorem splitNonempty {α : Type} (ts xs ys : List α)
    (hx : xs ≠ []) (hy : ys ≠ []) :
    (codeSplit ts xs ys).1 ≠ [] ∧ (codeSplit ts xs ys).2 ≠ [] := by
  induction ts generalizing xs ys with
  | nil => simpa [codeSplit] using And.intro hx hy
  | cons z zs ih => simpa [codeSplit] using ih (z :: ys) xs (by simp) hx

/-- Merge sorted code entries; ties choose the right list, as in HOL. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "code_merge_def"]
def codeMerge {α : Type} : List (Nat × α) → List (Nat × α) → List (Nat × α)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
      if x.1 < y.1 then x :: codeMerge xs (y :: ys) else y :: codeMerge (x :: xs) ys
termination_by xs ys => xs.length + ys.length
decreasing_by all_goals simp_wf <;> omega

/-- Sort code entries by location using the source split and tie policy. -/
@[hol "cakeml/compiler/backend/clos_to_bvlScript.sml" "code_sort_def"]
def codeSort {α : Type} (xs : List (Nat × α)) : List (Nat × α) :=
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
      codeMerge (codeSort (codeSplit rest [x] [y]).1) (codeSort (codeSplit rest [x] [y]).2)
termination_by xs.length
decreasing_by
  all_goals
    have hlen := splitLength rest [x] [y]
    have hnon := splitNonempty rest [x] [y] (by simp) (by simp)
    have hl : 0 < (codeSplit rest [x] [y]).1.length := List.length_pos_iff.mpr hnon.1
    have hr : 0 < (codeSplit rest [x] [y]).2.length := List.length_pos_iff.mpr hnon.2
    simp_wf
    simp only [List.length_cons, List.length_nil] at hlen
    omega

end Flapjack.Compiler.Backend.ClosToBvl

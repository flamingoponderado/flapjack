import Flapjack.Compiler.Backend.ClosToBvl.Sort
import Mathlib.Data.List.Permutation

/-! Permutation properties of the closure-code sort. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Alternating splitting preserves all entries, with their multiplicities. -/
theorem codeSplit_perm {α : Type} [DecidableEq α] (entries left right : List α) :
    ((codeSplit entries left right).1 ++ (codeSplit entries left right).2).Perm
      (entries ++ left ++ right) := by
  rw [List.perm_iff_count]
  intro value
  induction entries generalizing left right with
  | nil => simp [codeSplit]
  | cons first rest ih =>
    simp only [codeSplit, ih, List.count_append, List.count_cons]
    omega

/-- Merging two lists retains exactly their entries. -/
theorem codeMerge_perm {α : Type} [DecidableEq α] (left right : List (Nat × α)) :
    (codeMerge left right).Perm (left ++ right) := by
  fun_induction codeMerge left right with
  | case1 => simp
  | case2 => simp
  | case3 x xs y ys order ih => exact ih.cons x
  | case4 x xs y ys order ih =>
    exact (ih.cons y).trans (List.perm_middle.symm)

/-- Closure-code sorting preserves the entries and their multiplicities. -/
theorem codeSort_perm {α : Type} [DecidableEq α] (entries : List (Nat × α)) :
    (codeSort entries).Perm entries := by
  fun_induction codeSort entries with
  | case1 => simp
  | case2 x => simp
  | case3 x y rest ihLeft ihRight =>
    have rotated : (rest ++ [x] ++ [y]).Perm (x :: y :: rest) := by
      rw [List.perm_iff_count]
      intro entry
      simp only [List.count_append, List.count_cons, List.count_nil]
      omega
    exact (codeMerge_perm _ _).trans ((ihLeft.append ihRight).trans
      ((codeSplit_perm rest [x] [y]).trans rotated))

end Flapjack.Compiler.Backend.ClosToBvl

import Flapjack.HolRef
import Flapjack.Basis.Pure.MlList
import Flapjack.Misc.Sorting
import Flapjack.Misc.Mergesort

/-!
# `mllist$sort` sorts and is a permutation

Ports of `cakeml/basis/pure/mllistScript.sml:297-323`: for a transitive total relation
`sort` returns a sorted list, and it permutes its input, so membership and length are
preserved. A HOL relation `R : 'a -> 'a -> bool` used as a proposition is
`fun x y => R x y = true`, as in `Flapjack.Mergesort`. HOL `PERM` is the exact
`holPerm`. The permutation facts about the untagged mergesort helpers below are
Flapjack infrastructure (HOL proves them as `merge_tail_PERM`,
`sort2_tail_PERM`, `sort3_tail_PERM` and `mergesortN_tail_PERM` over the same
clauses).
-/

namespace Flapjack.Basis.Pure.MlList

private theorem perm_of_count {α : Type} {l1 l2 : List α}
    (h : ∀ [DecidableEq α] (a : α), l1.count a = l2.count a) : l1.Perm l2 := by
  classical
  exact List.perm_iff_count.mpr (fun a => h a)

private theorem sort2Tail_perm {α : Type} (neg : Bool) (r : α → α → Bool) (x y : α) :
    (sort2Tail neg r x y).Perm [x, y] := by
  unfold sort2Tail
  split
  · exact List.Perm.refl _
  · exact List.Perm.swap x y []

private theorem sort3Tail_perm {α : Type} (neg : Bool) (r : α → α → Bool) (x y z : α) :
    (sort3Tail neg r x y z).Perm [x, y, z] := by
  unfold sort3Tail
  repeat' split
  all_goals
    apply perm_of_count
    intro _ a
    (simp only [List.count_cons, List.count_nil]) <;> omega

private theorem mergeTail_perm {α : Type} (neg : Bool) (r : α → α → Bool) :
    ∀ (l1 l2 acc : List α), (mergeTail neg r l1 l2 acc).Perm (l1 ++ l2 ++ acc) := by
  intro l1 l2 acc
  fun_induction mergeTail neg r l1 l2 acc with
  | case1 acc => simp
  | case2 l acc _ => simpa using (List.reverse_perm l).append_right acc
  | case3 l acc _ => simpa using (List.reverse_perm l).append_right acc
  | case4 x l1 y l2 acc _ ih | case5 x l1 y l2 acc _ ih =>
      refine ih.trans (perm_of_count fun a => ?_)
      (simp only [List.count_append, List.count_cons]) <;> omega

private theorem mergesortNTail_perm {α : Type} (neg : Bool) (r : α → α → Bool) :
    ∀ (n : Nat) (l : List α), (mergesortNTail neg r n l).Perm (l.take n) := by
  intro n l
  fun_induction mergesortNTail neg r n l with
  | case4 ng x y _ => simpa using sort2Tail_perm ng r x y
  | case7 ng x y z _ => simpa using sort3Tail_perm ng r x y z
  | case8 ng x y => simpa using sort2Tail_perm ng r x y
  | case11 ng n l len1 neg' ih2 ih1 =>
      refine (mergeTail_perm _ r _ _ []).trans ?_
      rw [List.append_nil]
      refine (ih2.append ih1).trans ?_
      have hle : len1 ≤ n + 4 := Nat.div_le_self _ _
      have hsplit : n.succ.succ.succ.succ = len1 + (n + 4 - len1) := by omega
      rw [hsplit, List.take_add]
  | _ => simp

/-- Exact HOL `sort_PERM` (`mllistScript.sml:309-317`). -/
@[hol "cakeml/basis/pure/mllistScript.sml" "sort_PERM"]
theorem sortPerm {α : Type} : ∀ (R : α → α → Bool) (L : List α), holPerm L (sort R L) := by
  intro R L
  rw [holPerm_iff]
  have := mergesortNTail_perm false R L.length L
  rw [List.take_length] at this
  exact this.symm

/-- Exact HOL `sort_SORTED` (`mllistScript.sml:297-301`). -/
@[hol "cakeml/basis/pure/mllistScript.sml" "sort_SORTED"]
theorem sortSorted {α : Type} :
    ∀ (R : α → α → Bool) (L : List α),
      holTransitive (fun a b => R a b = true) ∧ holTotal (fun a b => R a b = true) →
      holSorted (fun a b => R a b = true) (sort R L) := by
  intro R L ⟨htr, hto⟩
  unfold sort mergesortTail
  rw [Mergesort.mergesortNCorrect false R L.length L ⟨hto, htr⟩]
  exact Mergesort.mergesortNSorted R L.length L ⟨hto, htr⟩

/-- Exact HOL `sort_MEM` (`mllistScript.sml:303-307`); `x` is free in HOL. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "sort_MEM"]
theorem sortMem {α : Type} (x : α) : ∀ (R : α → α → Bool) (L : List α), x ∈ sort R L ↔ x ∈ L := by
  intro R L
  exact ((holPerm_iff _ _).mp (sortPerm R L)).mem_iff.symm

/-- Exact HOL `sort_LENGTH` (`mllistScript.sml:319-323`). -/
@[hol "cakeml/basis/pure/mllistScript.sml" "sort_LENGTH"]
theorem sortLength {α : Type} : ∀ (R : α → α → Bool) (l : List α), (sort R l).length = l.length := by
  intro R l
  exact ((holPerm_iff _ _).mp (sortPerm R l)).length_eq.symm

end Flapjack.Basis.Pure.MlList

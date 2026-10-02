import Flapjack.HolRef
import Lean.Elab.Tactic.Omega

namespace Flapjack.Compiler.Backend.WordToStack

/-- Flapjack infrastructure: adjacent descending natural-key comparisons,
using the same zip/tail representation as sortedEnv. There is no separate
CakeML declaration for this generic Lean list helper. -/
def descendingKeys {α : Type} (xs : List (Nat × α)) : Prop :=
  (xs.zip xs.tail).all (fun (x, y) => decide (x.1 > y.1)) = true

private theorem descendingConsCons {α : Type} (x y : Nat × α) (ys : List (Nat × α)) :
    descendingKeys (x :: y :: ys) ↔ x.1 > y.1 ∧ descendingKeys (y :: ys) := by
  simp [descendingKeys]

/-- Full original descending-key head result: the tail is sorted, the head
is absent from it, and its key strictly exceeds every tail key. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTED_FST_LESS_IMP"]
theorem sortedFstLessImp {α : Type} (xs : List (Nat × α)) (x : Nat × α)
    (h : descendingKeys (x :: xs)) :
    descendingKeys xs ∧ x ∉ xs ∧ ∀ y, y ∈ xs → x.1 > y.1 := by
  have hb : ∀ y, y ∈ xs → x.1 > y.1 := by
    induction xs generalizing x with
    | nil => simp
    | cons z zs ih =>
      obtain ⟨hxz, hzs⟩ := (descendingConsCons x z zs).mp h
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hxz
      · exact Nat.lt_trans (ih z hzs y hy) hxz
  have ht : descendingKeys xs := by
    cases xs with
    | nil => simp [descendingKeys]
    | cons y ys => exact (descendingConsCons x y ys).mp h |>.2
  refine ⟨ht, ?_, hb⟩
  intro hx
  have := hb x hx
  omega

/-- Full original uniqueness theorem for lists sorted by strictly descending
natural keys, under exactly pointwise equivalence of element membership. -/
@[hol "cakeml/compiler/backend/proofs/word_to_stackProofScript.sml" "SORTED_IMP_EQ_LISTS"]
theorem sortedImpEqLists {α : Type} (xs ys : List (Nat × α))
    (hy : descendingKeys ys) (hx : descendingKeys xs)
    (hm : ∀ x, x ∈ ys ↔ x ∈ xs) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys => have := (hm y).mp (List.mem_cons_self); simp at this
  | cons x xs ih =>
    cases ys with
    | nil => have := (hm x).mpr (List.mem_cons_self); simp at this
    | cons y ys =>
      obtain ⟨hxs, hnx, hxb⟩ := sortedFstLessImp xs x hx
      obtain ⟨hys, hny, hyb⟩ := sortedFstLessImp ys y hy
      have heq : x = y := by
        apply Classical.byContradiction
        intro hne
        have hxy : x ∈ ys := by
          have := (hm x).mpr (List.mem_cons_self)
          simp only [List.mem_cons] at this
          exact this.resolve_left hne
        have hyx : y ∈ xs := by
          have := (hm y).mp (List.mem_cons_self)
          simp only [List.mem_cons] at this
          exact this.resolve_left (Ne.symm hne)
        have := hxb y hyx
        have := hyb x hxy
        omega
      subst y
      congr 1
      apply ih ys hys hxs
      intro z
      by_cases hz : z = x
      · subst z; simp [hnx, hny]
      · simpa [List.mem_cons, hz] using hm z

end Flapjack.Compiler.Backend.WordToStack

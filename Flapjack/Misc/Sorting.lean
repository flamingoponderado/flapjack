import Flapjack.HolRef
import Flapjack.Misc.Relation

/-!
# HOL sorting `SORTED`, `PART` and `PARTITION`

Exact ports of `HOL/src/sort/sortingScript.sml` `SORTED_DEF` (564-568),
`PART_DEF` (643-648) and `PARTITION_DEF` (740-741), with the theorems
`SORTED_EQ` (588-596) and `SORTED_TL` (1117-1121), cited in the pinned
upstream HOL submodule. HOL relations `'a -> 'a -> bool` are rendered as
`α → α → Prop`; the partition predicate `'a -> bool` is a `Bool`-valued
function, so `if P h` is the Boolean branch. All three are total and fully
specified.
-/

namespace Flapjack

/-- Exact HOL `SORTED_DEF` (`sortingScript.sml:564-568`): every adjacent pair is
related; no transitivity is assumed. -/
@[hol "HOL/src/sort/sortingScript.sml" "SORTED_DEF"]
def holSorted {α : Type} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => R x y ∧ holSorted R (y :: rest)

/-- Exact HOL `SORTED_EQ` (`sortingScript.sml:588-596`); HOL `transitive` is the
tagged `holTransitive`. -/
@[hol "HOL/src/sort/sortingScript.sml" "SORTED_EQ"]
theorem holSortedEq {α : Type} :
    ∀ (R : α → α → Prop) (L : List α) (x : α),
      holTransitive R → (holSorted R (x :: L) ↔ holSorted R L ∧ ∀ y, y ∈ L → R x y) := by
  intro R L
  induction L with
  | nil => intro x _; simp [holSorted]
  | cons h t ih =>
      intro x htr
      simp only [holSorted, List.mem_cons]
      constructor
      · rintro ⟨hxh, hs⟩
        refine ⟨hs, fun y hy => ?_⟩
        rcases hy with rfl | hy
        · exact hxh
        · exact htr x h y ⟨hxh, ((ih h htr).mp hs).2 y hy⟩
      · rintro ⟨hs, hall⟩
        exact ⟨hall h (Or.inl rfl), hs⟩

/-- Exact HOL `SORTED_TL` (`sortingScript.sml:1117-1121`). -/
@[hol "HOL/src/sort/sortingScript.sml" "SORTED_TL"]
theorem holSortedTl {α : Type} (R : α → α → Prop) (x : α) (xs : List α) :
    holSorted R (x :: xs) → holSorted R xs := by
  cases xs with
  | nil => intro _; trivial
  | cons y rest => exact fun h => h.2

/-- Exact HOL `PART_DEF` (`sortingScript.sml:643-648`): each element is
prepended to the accumulator its predicate selects, so both buckets come out
reversed. -/
@[hol "HOL/src/sort/sortingScript.sml" "PART_DEF"]
def holPart {α : Type} (P : α → Bool) : List α → List α → List α → List α × List α
  | [], l1, l2 => (l1, l2)
  | h :: rst, l1, l2 => if P h then holPart P rst (h :: l1) l2 else holPart P rst l1 (h :: l2)

/-- Exact HOL `PARTITION_DEF` (`sortingScript.sml:740-741`). -/
@[hol "HOL/src/sort/sortingScript.sml" "PARTITION_DEF"]
def holPartition {α : Type} (P : α → Bool) (l : List α) : List α × List α :=
  holPart P l [] []

end Flapjack

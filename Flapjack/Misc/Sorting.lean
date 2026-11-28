module

public import Flapjack.HolRef
public import Flapjack.Misc.Relation
public import Flapjack.Misc.List

@[expose] public section

/-!
# HOL sorting `SORTED`, `PART` and `PARTITION`

Exact ports of `HOL/src/sort/sortingScript.sml` `SORTED_DEF` (564-568),
`SORTS_DEF` (570-572),
`PART_DEF` (643-648) and `PARTITION_DEF` (740-741), with the theorems
`SORTED_EQ` (588-596) and `SORTED_TL` (1117-1121), and `PERM_DEF` (17-18),
cited in the pinned upstream HOL submodule. HOL relations `'a -> 'a -> bool` are rendered as
`α → α → Prop` (and `SORTS`'s comparator as a `Bool`-valued function); the
partition predicate `'a -> bool` is a `Bool`-valued
function, so `if P h` is the Boolean branch. All are total and fully
specified.
-/

namespace Flapjack

open Classical in
/-- Exact HOL `PERM_DEF` (`sortingScript.sml:17-18`):
`PERM L1 L2 = !x. FILTER ($= x) L1 = FILTER ($= x) L2`. HOL equality is a
total boolean test; the filter predicate decides it classically. -/
@[hol "HOL/src/sort/sortingScript.sml" "PERM_DEF"]
def holPerm {α : Type} (L1 L2 : List α) : Prop :=
  ∀ x, L1.filter (fun y => decide (x = y)) = L2.filter (fun y => decide (x = y))

/-- HOL `PERM` is the core `List.Perm`. Flapjack infrastructure, not a HOL
theorem. -/
theorem holPerm_iff {α : Type} (L1 L2 : List α) : holPerm L1 L2 ↔ L1.Perm L2 := by
  classical
  have key : ∀ (l : List α) (x : α),
      l.filter (fun y => decide (x = y)) = List.replicate (l.count x) x := by
    intro l x
    induction l with
    | nil => rfl
    | cons h t ih =>
      by_cases e : x = h
      · subst e; simp [ih, List.replicate_succ]
      · simp [e, ih, Ne.symm e]
  unfold holPerm
  rw [List.perm_iff_count]
  constructor
  · intro h x
    have := congrArg List.length (h x)
    simpa [key] using this
  · intro h x
    rw [key, key, h x]

/-- Exact HOL `SORTED_DEF` (`sortingScript.sml:564-568`): every adjacent pair is
related; no transitivity is assumed. -/
@[hol "HOL/src/sort/sortingScript.sml" "SORTED_DEF"]
def holSorted {α : Type} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => R x y ∧ holSorted R (y :: rest)

/-- Exact HOL `SORTS_DEF` (`sortingScript.sml:570-572`):
`SORTS f R = !l. PERM l (f R l) /\ SORTED R (f R l)`. The sorting function
`f` takes the HOL boolean comparator and a list. -/
@[hol "HOL/src/sort/sortingScript.sml" "SORTS_DEF"]
def holSorts {α : Type} (f : (α → α → Bool) → List α → List α)
    (R : α → α → Bool) : Prop :=
  ∀ l, holPerm l (f R l) ∧ holSorted (fun a b => R a b = true) (f R l)

/-- Pairwise related elements are adjacent-sorted. This is Flapjack
infrastructure relating Lean's list predicate to HOL's `SORTED`. -/
theorem holSorted_of_pairwise {α : Type} (R : α → α → Prop) :
    ∀ xs : List α, xs.Pairwise R → holSorted R xs
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: rest, pairwise =>
    ⟨(List.pairwise_cons.mp pairwise).1 y (by simp),
      holSorted_of_pairwise R (y :: rest) (List.pairwise_cons.mp pairwise).2⟩

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

/-- Under a transitive relation, HOL's adjacent sorting entails pairwise
relatedness. This is Flapjack infrastructure for Lean list reasoning. -/
theorem pairwise_of_holSorted {α : Type} (R : α → α → Prop) (trans : holTransitive R) :
    ∀ xs : List α, holSorted R xs → xs.Pairwise R
  | [], _ => .nil
  | x :: xs, sorted =>
    let parts := (holSortedEq R xs x trans).mp sorted
    List.pairwise_cons.mpr ⟨parts.2, pairwise_of_holSorted R trans xs parts.1⟩

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

/-- Flapjack infrastructure: appending an element greater than every existing
one preserves HOL adjacent-pair sortedness. -/
private theorem holSorted_append_greater {α : Type} (R : α → α → Prop) (x : α) :
    ∀ l : List α, holSorted R l → (∀ y, y ∈ l → R y x) → holSorted R (l ++ [x])
  | [], _, _ => trivial
  | [a], _, hx => by
      simp only [List.cons_append, List.nil_append, holSorted]
      exact ⟨hx a (by simp), trivial⟩
  | a :: b :: rest, hl, hx => by
      simp only [List.cons_append, holSorted] at hl ⊢
      exact ⟨hl.1,
        holSorted_append_greater R x (b :: rest) hl.2 (fun y hy => hx y (by simp [hy]))⟩

/-- Original `SORTED_inv_image_LESS_PLUS`: shifting by a constant does not
change which lists are sorted by `<`. -/
@[hol "cakeml/misc/miscScript.sml" "SORTED_inv_image_LESS_PLUS"]
theorem sortedInvImage_less_add (k : Nat) :
    holSorted (InvImage (· < ·) (fun x => k + x)) = holSorted (· < ·) := by
  funext l
  apply propext
  induction l with
  | nil => exact Iff.rfl
  | cons x xs ih =>
    cases xs with
    | nil => exact Iff.rfl
    | cons y rest =>
      simp only [holSorted, InvImage, Nat.add_lt_add_iff_left]
      rw [ih]

/-- Original `SORTED_GENLIST_TIMES`: multiplying the generated indices by a
positive constant keeps them sorted. -/
@[hol "cakeml/misc/miscScript.sml" "SORTED_GENLIST_TIMES"]
theorem sortedGenlistTimes (k n : Nat) (hk : 0 < k) :
    holSorted (· < ·) (genlist (fun x => k * x) n) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    exact holSorted_append_greater (· < ·) (k * n) (genlist (fun x => k * x) n) ih (by
      intro y hy
      rw [genlist_range] at hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      rw [List.mem_range] at hi
      exact Nat.mul_lt_mul_of_pos_left hi hk)

end Flapjack

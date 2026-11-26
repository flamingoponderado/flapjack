module

public import Flapjack.Misc.FindIndex
public import Flapjack.Misc.FindIndex.Bounds

@[expose] public section

namespace Flapjack.Misc

/-- Full append equation at any starting offset. A match in the first list
wins; otherwise search resumes after its entire length. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_APPEND"]
theorem findIndexAppend {α : Type} [DecidableEq α]
    (left right : List α) (target : α) (offset : Nat) :
    findIndex target (left ++ right) offset =
      match findIndex target left offset with
      | none => findIndex target right (offset + left.length)
      | some index => some index := by
  induction left generalizing offset with
  | nil => simp [findIndex]
  | cons head tail ih =>
      by_cases equal : head = target
      · simp [findIndex, equal]
      · simpa [findIndex, equal, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (offset + 1)

/-- A found index is never below its starting offset. -/
private theorem findIndex_some_ge {α : Type} [DecidableEq α] (target : α) :
    ∀ (ls : List α) (m i : Nat), findIndex target ls m = some i → m ≤ i := by
  intro ls
  induction ls with
  | nil =>
    intro m i h
    simp [findIndex] at h
  | cons a t ih =>
    intro m i h
    by_cases ha : a = target
    · simp [findIndex, ha] at h
      omega
    · simp only [findIndex, if_neg ha] at h
      have := ih (m + 1) i h
      omega

/-- Original `find_index_APPEND1`: a match inside the left list is found by the
left list alone. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_APPEND1"]
theorem findIndex_append1 {α : Type} [DecidableEq α] (target : α) :
    ∀ (l1 l2 : List α) (m i : Nat), findIndex target (l1 ++ l2) m = some i →
      i < m + l1.length → findIndex target l1 m = some i := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 m i h hi
    have hge := findIndex_some_ge target l2 m i h
    simp only [List.length_nil, Nat.add_zero] at hi
    exact absurd hge (by omega)
  | cons a t ih =>
    intro l2 m i h hi
    by_cases ha : a = target
    · simp [findIndex, ha] at h ⊢
      exact h
    · simp only [findIndex, if_neg ha, List.cons_append, List.length_cons] at h hi ⊢
      exact ih l2 (m + 1) i h (by omega)

/-- Original `find_index_APPEND2`: a match at or after the start of the right
list is found in the right list alone, searched from the same absolute offset.
The HOL conjunction premise becomes two hypotheses. -/
@[hol "cakeml/misc/miscScript.sml" "find_index_APPEND2"]
theorem findIndex_append2 {α : Type} [DecidableEq α] (target : α) :
    ∀ (l1 l2 : List α) (m i : Nat), findIndex target (l1 ++ l2) m = some i →
      m + l1.length ≤ i → findIndex target l2 (m + l1.length) = some i := by
  intro l1 l2 m i hfound hbound
  rw [findIndexAppend] at hfound
  cases hleft : findIndex target l1 m with
  | none => simpa only [hleft] using hfound
  | some index =>
    simp only [hleft, Option.some.injEq] at hfound
    have below := (findIndexLessLength l1 target m index hleft).2
    exfalso
    omega

end Flapjack.Misc

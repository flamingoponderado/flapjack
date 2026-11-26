module

public import Flapjack.HolRef

@[expose] public section

/-!
# `anub`: first-binding association lists

Counterpart of `anub` in `cakeml/misc/miscScript.sml`: keep the first binding of each key,
skipping keys already in the accumulator.
-/

namespace Flapjack

/-- Exact HOL `anub_def` (`miscScript.sml:684-689`). -/
@[hol "cakeml/misc/miscScript.sml" "anub_def"]
def anub {α β : Type} [DecidableEq α] : List (α × β) → List α → List (α × β)
  | [], _ => []
  | (k, v) :: ls, acc => if k ∈ acc then anub ls acc else (k, v) :: anub ls (k :: acc)

/-- Exact HOL `anub_all_distinct_keys` (`miscScript.sml:764-775`); HOL `ALL_DISTINCT` is
`List.Nodup`. -/
@[hol "cakeml/misc/miscScript.sml" "anub_all_distinct_keys"]
theorem anubAllDistinctKeys {α β : Type} [DecidableEq α] :
    ∀ (ls : List (α × β)) (acc : List α), acc.Nodup → ((anub ls acc).map Prod.fst ++ acc).Nodup
  | [], acc, h => by simpa [anub] using h
  | (k, v) :: ls, acc, h => by
      unfold anub
      by_cases hk : k ∈ acc
      · rw [if_pos hk]; exact anubAllDistinctKeys ls acc h
      · rw [if_neg hk]
        have ih := anubAllDistinctKeys ls (k :: acc) (List.nodup_cons.mpr ⟨hk, h⟩)
        rw [List.map_cons, List.cons_append]
        exact List.perm_middle.nodup_iff.mp ih

/-- Original `anub_eq_nil`: the pruned list is empty exactly when every key is
already in the accumulator. -/
@[hol "cakeml/misc/miscScript.sml" "anub_eq_nil"]
theorem anub_eq_nil {α β : Type} [DecidableEq α] (x : List (α × β)) (y : List α) :
    anub x y = [] ↔ ∀ k ∈ x.map Prod.fst, k ∈ y := by
  induction x generalizing y with
  | nil => simp [anub]
  | cons p rest ih =>
    rcases p with ⟨a, b⟩
    by_cases ha : a ∈ y
    · simp [anub, ha, ih y]
    · simp [anub, ha]

/-- Original `anub_notin_acc`: keys already in the accumulator never reappear. -/
@[hol "cakeml/misc/miscScript.sml" "anub_notin_acc"]
theorem anub_notin_acc {α β : Type} [DecidableEq α] (x : α) :
    ∀ (ls : List (α × β)) (acc : List α), x ∈ acc → x ∉ (anub ls acc).map Prod.fst := by
  intro ls
  induction ls with
  | nil =>
    intro acc _
    simp [anub]
  | cons p rest ih =>
    intro acc h
    rcases p with ⟨k, v⟩
    by_cases hk : k ∈ acc
    · simp only [anub, if_pos hk]
      exact ih acc h
    · simp only [anub, if_neg hk, List.map_cons, List.mem_cons, not_or]
      refine ⟨?_, ih (k :: acc) (List.mem_cons_of_mem k h)⟩
      intro hxk
      exact hk (hxk ▸ h)

end Flapjack

import Flapjack.HolRef

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

end Flapjack

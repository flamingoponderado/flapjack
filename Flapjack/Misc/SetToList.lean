module

public import Flapjack.Misc.PredSetChoice
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# HOL list `SET_TO_LIST`

Counterpart for the `SET_TO_LIST` group of the pinned original HOL
`src/list/src/listScript.sml` (lines 2750-2865). HOL defines

```
SET_TO_LIST s = if FINITE s then if s = {} then []
                                 else CHOICE s :: SET_TO_LIST (REST s)
                else ARB
```

by well-founded recursion on `CARD`. The Lean rendering follows the same
clauses over the reviewed `holChoice`/`holRest`, with `FINITE` as
`Set.Finite`, `CARD` as `Set.ncard`, `ARB` as `holArb` and `MEM` as list
membership. The element order is the one determined by `CHOICE`, as in HOL.
-/

namespace Flapjack

open Classical in
/-- HOL `SET_TO_LIST` (`listScript.sml:2757-2762`). -/
@[hol "HOL/src/list/src/listScript.sml" "SET_TO_LIST_defn"
  (total_function_inhabitants := [α])]
noncomputable def holSetToList {α : Type} [Nonempty α] (s : Set α) : List α :=
  if _ : s.Finite then
    if _ : s = ∅ then [] else holChoice s :: holSetToList (holRest s)
  else holArb (List α)
termination_by s.ncard
decreasing_by
  exact Set.ncard_sdiff_singleton_lt_of_mem (holChoice_mem s ‹¬s = ∅›) ‹s.Finite›

open Classical in
/-- Exact HOL `SET_TO_LIST_THM` (`listScript.sml:2782-2783`): the recursion
equation on finite sets; the HOL free variable `s` is universally quantified. -/
@[hol "HOL/src/list/src/listScript.sml" "SET_TO_LIST_THM"
  (total_function_inhabitants := [α])]
theorem holSetToList_thm {α : Type} [Nonempty α] {s : Set α} :
    s.Finite → holSetToList s = if s = ∅ then [] else holChoice s :: holSetToList (holRest s) := by
  intro hf
  rw [holSetToList, dif_pos hf]
  by_cases hs : s = ∅
  · rw [dif_pos hs, if_pos hs]
  · rw [dif_neg hs, if_neg hs]

/-- Exact HOL `SET_TO_LIST_IN_MEM` (`listScript.sml:2827-2835`). -/
@[hol "HOL/src/list/src/listScript.sml" "SET_TO_LIST_IN_MEM"
  (total_function_inhabitants := [α])]
theorem holSetToList_in_mem {α : Type} [Nonempty α] :
    ∀ s : Set α, s.Finite → ∀ x, x ∈ s ↔ x ∈ holSetToList s := by
  intro s
  induction h : s.ncard using Nat.strongRecOn generalizing s with
  | ind n ih =>
    intro hf x
    rw [holSetToList_thm hf]
    by_cases hs : s = ∅
    · simp [hs]
    · rw [if_neg hs]
      have hmem := holChoice_mem s hs
      have hlt : (holRest s).ncard < n := by
        rw [← h]; exact Set.ncard_sdiff_singleton_lt_of_mem hmem hf
      have hrest : (holRest s).Finite := hf.sdiff
      rw [List.mem_cons, ← ih _ hlt (holRest s) rfl hrest x]
      simp only [holRest, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · intro hx
        by_cases hxc : x = holChoice s
        · exact Or.inl hxc
        · exact Or.inr ⟨hx, hxc⟩
      · rintro (rfl | ⟨hx, _⟩)
        · exact hmem
        · exact hx

/-- Exact HOL `MEM_SET_TO_LIST` (`listScript.sml:2839-2842`). -/
@[hol "HOL/src/list/src/listScript.sml" "MEM_SET_TO_LIST"
  (total_function_inhabitants := [α])]
theorem mem_holSetToList {α : Type} [Nonempty α] :
    ∀ s : Set α, s.Finite → ∀ x, x ∈ holSetToList s ↔ x ∈ s :=
  fun s hf x => (holSetToList_in_mem s hf x).symm

end Flapjack

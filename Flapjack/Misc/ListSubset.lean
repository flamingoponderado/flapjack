module

public import Flapjack.HolRef

@[expose] public section

/-!
# Faithful Cake `list_subset` (`misc`)

Exact definition from `cakeml/misc/miscScript.sml:3092`. `list_subset l1 l2`
holds when every element of `l1` is a member of `l2`. The type is fully
polymorphic in HOL (`'a list -> 'a list -> bool`), so the definition carries no
type-indexed word and needs no carrier qualifier: HOL `EVERY (\x. MEM x l2) l1`
is Lean `l1.all (fun x => decide (x ∈ l2))`, with HOL's decidable equality
rendered by `[DecidableEq α]`.
-/

namespace Flapjack.Misc

/-- Exact HOL `misc$list_subset_def` (`miscScript.sml:3092`):
`list_subset l1 l2 = EVERY (\x. MEM x l2) l1`. -/
@[hol "cakeml/misc/miscScript.sml" "list_subset_def"]
def listSubset {α : Type} [DecidableEq α] (l1 l2 : List α) : Bool :=
  l1.all (fun x => decide (x ∈ l2))

/-- Exact HOL `misc$list_set_eq_def` (`miscScript.sml:3096`): mutual list
containment. -/
@[hol "cakeml/misc/miscScript.sml" "list_set_eq_def"]
def listSetEq {α : Type} [DecidableEq α] (l1 l2 : List α) : Bool :=
  listSubset l1 l2 && listSubset l2 l1

/-- Original `list_subset_LENGTH`: a distinct list contained in another is no
longer than it. -/
@[hol "cakeml/misc/miscScript.sml" "list_subset_LENGTH"]
theorem listSubsetLength {α : Type} [DecidableEq α] (l1 l2 : List α)
    (h : l1.Nodup ∧ listSubset l1 l2 = true) : l1.length ≤ l2.length := by
  obtain ⟨hnd, hsub⟩ := h
  induction l1 generalizing l2 with
  | nil => simp
  | cons a as ih =>
    rw [List.nodup_cons] at hnd
    simp only [listSubset, List.all_eq_true, List.mem_cons,
      decide_eq_true_eq] at hsub
    have ha : a ∈ l2 := hsub a (Or.inl rfl)
    have htail : ∀ x, x ∈ as → x ∈ l2 := fun x hx => hsub x (Or.inr hx)
    have hfilt : (l2.filter (fun x => x ≠ a)).length < l2.length := by
      have hle := List.length_filter_le (fun x => x ≠ a) l2
      have hne : (l2.filter (fun x => x ≠ a)).length ≠ l2.length := by
        intro heq
        have h := (List.length_filter_eq_length_iff.mp heq) a ha
        simp at h
      omega
    have hsub' : listSubset as (l2.filter (fun x => x ≠ a)) = true := by
      simp only [listSubset, List.all_eq_true, List.mem_filter, decide_eq_true_eq]
      intro x hx
      refine ⟨htail x hx, ?_⟩
      intro heq
      exact hnd.1 (heq ▸ hx)
    have := ih (l2.filter (fun x => x ≠ a)) hnd.2 hsub'
    simp only [List.length_cons]
    omega

end Flapjack.Misc

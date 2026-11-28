module

public import Flapjack.HolRef
public import Flapjack.Misc.ListEl
public import Mathlib.Data.List.Basic

@[expose] public section

/-!
# `is_subseq`: one list contained as a subsequence of another

Counterparts of `is_subseq_def` and its lemmas in
`cakeml/misc/miscScript.sml:3404-3480`. HOL's `is_subseq l1 l2` says that `l2`
is a subsequence of `l1`; the Lean rendering `isSubseq l1 l2` keeps the same
clauses and returns a `Bool`, so the theorems state `isSubseq … = true`.
`isSubseq_iff_sublist` bridges it to Mathlib's `List.Sublist`, whose first
argument is the subsequence. HOL's `IS_PREFIX l1 l2` is `isPREFIX l2 l1` (the
arguments are flipped by the `rich_listTheory` overload), so it becomes
`l2.IsPrefix l1`; `IS_SUBLIST l1 l2` is the contiguous-sublist relation, so it
becomes `l2.IsInfix l1`.
-/

namespace Flapjack

/-- Exact HOL `is_subseq_def` (`miscScript.sml:3404-3410`): the second list is
a subsequence of the first. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_def"]
def isSubseq {α : Type} [DecidableEq α] : List α → List α → Bool
  | _, [] => true
  | [], _ :: _ => false
  | y :: ys, x :: xs => (x = y && isSubseq ys xs) || isSubseq ys (x :: xs)
termination_by l1 l2 => l1.length + l2.length

/-- `isSubseq l1 l2` is Mathlib's `l2.Sublist l1`. -/
theorem isSubseq_iff_sublist {α : Type} [DecidableEq α] (l1 l2 : List α) :
    isSubseq l1 l2 = true ↔ l2.Sublist l1 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => simp [isSubseq]
    | cons x xs => simp [isSubseq]
  | cons y ys ih =>
    cases l2 with
    | nil => simp [isSubseq]
    | cons x xs =>
      simp only [isSubseq, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨hxy, h⟩ | h)
        · rw [← hxy]
          exact List.Sublist.cons_cons x ((ih xs).mp h)
        · exact List.Sublist.cons y ((ih (x :: xs)).mp h)
      · intro h
        cases h with
        | cons a h' => exact Or.inr ((ih (x :: xs)).mpr h')
        | cons_cons a h' => exact Or.inl ⟨rfl, (ih xs).mpr h'⟩

/-- Original `is_subseq_refl`: every list contains itself. -/
@[simp, hol "cakeml/misc/miscScript.sml" "is_subseq_refl"]
theorem isSubseq_refl {α : Type} [DecidableEq α] (l : List α) : isSubseq l l = true :=
  (isSubseq_iff_sublist l l).mpr (List.Sublist.refl l)

/-- Original `is_subseq_nil`: only the empty list is a subsequence of `[]`. -/
@[simp, hol "cakeml/misc/miscScript.sml" "is_subseq_nil"]
theorem isSubseq_nil {α : Type} [DecidableEq α] (l : List α) :
    isSubseq [] l = true ↔ l = [] :=
  (isSubseq_iff_sublist [] l).trans List.sublist_nil

/-- Original `is_subseq_cons`: prefixing the container preserves subsequences. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_cons"]
theorem isSubseq_cons {α : Type} [DecidableEq α] (l1 l2 : List α) (x : α)
    (h : isSubseq l1 l2 = true) : isSubseq (x :: l1) l2 = true :=
  (isSubseq_iff_sublist (x :: l1) l2).mpr
    (List.Sublist.cons x ((isSubseq_iff_sublist l1 l2).mp h))

/-- Original `is_subseq_snoc`: appending to the container preserves
subsequences. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_snoc"]
theorem isSubseq_snoc {α : Type} [DecidableEq α] (l1 l2 : List α) (x : α)
    (h : isSubseq l1 l2 = true) : isSubseq (l1 ++ [x]) l2 = true :=
  (isSubseq_iff_sublist (l1 ++ [x]) l2).mpr
    (((isSubseq_iff_sublist l1 l2).mp h).trans (List.sublist_append_left l1 [x]))

/-- Original `is_subseq_append1`: a left append keeps subsequences. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_append1"]
theorem isSubseq_append1 {α : Type} [DecidableEq α] (l3 l1 l2 : List α)
    (h : isSubseq l1 l2 = true) : isSubseq (l3 ++ l1) l2 = true :=
  (isSubseq_iff_sublist (l3 ++ l1) l2).mpr
    (((isSubseq_iff_sublist l1 l2).mp h).trans (List.sublist_append_right l3 l1))

/-- Original `is_subseq_append2`: a right append keeps subsequences. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_append2"]
theorem isSubseq_append2 {α : Type} [DecidableEq α] (l4 l1 l2 : List α)
    (h : isSubseq l1 l2 = true) : isSubseq (l1 ++ l4) l2 = true :=
  (isSubseq_iff_sublist (l1 ++ l4) l2).mpr
    (((isSubseq_iff_sublist l1 l2).mp h).trans (List.sublist_append_left l1 l4))

/-- Original `is_subseq_IS_SUBLIST`: a contiguous sublist of a subsequence is a
subsequence. HOL's `IS_SUBLIST l3 l1` says `l1` is contiguous in `l3`. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_IS_SUBLIST"]
theorem isSubseq_isInfix {α : Type} [DecidableEq α] (l1 l2 l3 : List α)
    (h : isSubseq l1 l2 = true ∧ l1.IsInfix l3) : isSubseq l3 l2 = true := by
  obtain ⟨h, hin⟩ := h
  exact (isSubseq_iff_sublist l3 l2).mpr
    (((isSubseq_iff_sublist l1 l2).mp h).trans hin.sublist)

/-- Original `is_subseq_MEM`: a subsequence only contains members of the
container. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_MEM"]
theorem isSubseq_mem {α : Type} [DecidableEq α] (l1 l2 : List α) (x : α)
    (h : isSubseq l1 l2 = true ∧ x ∈ l2) : x ∈ l1 := by
  obtain ⟨h, hm⟩ := h
  exact ((isSubseq_iff_sublist l1 l2).mp h).subset hm

/-- Original `IS_PREFIX_is_subseq`: a prefix of the container is a subsequence.
HOL's `IS_PREFIX l1 l2` is `l2` being a prefix of `l1`. -/
@[hol "cakeml/misc/miscScript.sml" "IS_PREFIX_is_subseq"]
theorem isPrefix_isSubseq {α : Type} [DecidableEq α] (l1 l2 : List α)
    (hp : l2.IsPrefix l1) : isSubseq l1 l2 = true :=
  (isSubseq_iff_sublist l1 l2).mpr hp.sublist

/-- Original `IS_SUBLIST_is_subseq`: a contiguous sublist is a subsequence. -/
@[hol "cakeml/misc/miscScript.sml" "IS_SUBLIST_is_subseq"]
theorem isInfix_isSubseq {α : Type} [DecidableEq α] (l1 l2 : List α)
    (hin : l2.IsInfix l1) : isSubseq l1 l2 = true :=
  (isSubseq_iff_sublist l1 l2).mpr hin.sublist

/-- Original `is_subseq_ALL_DISTINCT`: a subsequence of a distinct list is
distinct. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_ALL_DISTINCT"]
theorem isSubseq_allDistinct {α : Type} [DecidableEq α] (l1 l2 : List α)
    (h : l1.Nodup ∧ isSubseq l1 l2 = true) : l2.Nodup := by
  obtain ⟨hnd, h⟩ := h
  exact ((isSubseq_iff_sublist l1 l2).mp h).nodup hnd

/-- Original `is_subseq_append_suff`: appending subsequences pairwise is a
subsequence. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_append_suff"]
theorem isSubseq_append_suff {α : Type} [DecidableEq α] (l1 l3 l2 l4 : List α)
    (h : isSubseq l1 l3 = true ∧ isSubseq l2 l4 = true) :
    isSubseq (l1 ++ l2) (l3 ++ l4) = true := by
  obtain ⟨h1, h2⟩ := h
  exact (isSubseq_iff_sublist (l1 ++ l2) (l3 ++ l4)).mpr
    (((isSubseq_iff_sublist l1 l3).mp h1).append ((isSubseq_iff_sublist l2 l4).mp h2))

/-- Original `is_subseq_FLAT_suff`: flattening pairwise subsequences is a
subsequence. -/
@[hol "cakeml/misc/miscScript.sml" "is_subseq_FLAT_suff"]
theorem isSubseq_flat_suff {α : Type} [DecidableEq α] (ls1 ls2 : List (List α))
    (h : List.Forall₂ (fun x y => isSubseq x y = true) ls1 ls2) :
    isSubseq ls1.flatten ls2.flatten = true := by
  induction h with
  | nil =>
    rw [List.flatten_nil]
    exact isSubseq_refl []
  | cons hhead htail ih =>
    rw [List.flatten_cons, List.flatten_cons]
    exact isSubseq_append_suff _ _ _ _ ⟨hhead, ih⟩

/-- Original `IS_PREFIX_THM`: a prefix is exactly a shorter list with matching
elements at every position of the shorter one. -/
@[hol "cakeml/misc/miscScript.sml" "IS_PREFIX_THM"
  (total_function_inhabitants := [α])]
theorem isPrefixThm {α : Type} [Nonempty α] (l2 l1 : List α) :
    l2.IsPrefix l1 ↔ l2.length ≤ l1.length ∧ ∀ n, n < l2.length → holEl n l2 = holEl n l1 := by
  induction l2 generalizing l1 with
  | nil =>
    constructor
    · intro _
      exact ⟨by simp, by simp⟩
    · intro _
      exact List.nil_prefix
  | cons b bs ih =>
    cases l1 with
    | nil =>
      constructor
      · intro h
        have := h.length_le
        simp at this
      · intro h
        simp at h
    | cons a as =>
      rw [List.cons_prefix_cons]
      constructor
      · rintro ⟨rfl, htail⟩
        constructor
        · simp only [List.length_cons]
          have := htail.length_le
          omega
        · intro n hn
          cases n with
          | zero => simp only [holEl, holHd]
          | succ m =>
            have hm : m < bs.length := by simpa using hn
            have h := (ih as).mp htail
            have h2 := h.2 m hm
            simpa only [holEl_cons_succ] using h2
      · rintro ⟨hlen, hel⟩
        have hb : b = a := by
          have h := hel 0 (by simp)
          simpa only [holEl, holHd] using h
        subst hb
        refine ⟨rfl, (ih as).mpr ⟨?_, ?_⟩⟩
        · simp only [List.length_cons] at hlen
          omega
        · intro m hm
          have h := hel (m + 1) (by simpa using hm)
          simpa only [holEl_cons_succ] using h

end Flapjack

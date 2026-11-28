module

public import Flapjack.HolRef
public import Mathlib.Data.List.Basic
public import Flapjack.Misc.ListEl

@[expose] public section

namespace Flapjack

/-- Exact HOL `FOLDL_invariant` (`miscScript.sml:1471-1477`): a property
preserved by every step of a left fold from a good start holds of the result.
HOL's `bool`-valued `P` is kept as a `Bool` predicate, so the hypotheses state
`P x = true`; the single HOL conjunction premise becomes two Lean hypotheses. -/
@[hol "cakeml/misc/miscScript.sml" "FOLDL_invariant"]
theorem foldl_invariant {α β : Type} (P : α → Bool) (f : α → β → α) :
    ∀ (ls : List β) (a : α), P a = true ∧
      (∀ (x : α) (y : β), y ∈ ls ∧ P x = true → P (f x y) = true) →
        P (ls.foldl f a) = true := by
  intro ls
  induction ls with
  | nil =>
    intro a h
    obtain ⟨hstart, _⟩ := h
    exact hstart
  | cons y ys ih =>
    intro a h
    obtain ⟨hstart, hstep⟩ := h
    simp only [List.foldl_cons]
    exact ih (f a y) ⟨hstep a y ⟨by simp, hstart⟩,
      fun x z hz => hstep x z ⟨by simp [hz.1], hz.2⟩⟩

/-- Original `FOLDL_invariant_rest`: a property indexed by a suffix of the
list, preserved from the whole list down to the empty suffix, holds of the
fold result on the empty suffix. HOL's `EL n ls` is `holEl n ls`, which needs
an inhabited element type. -/
@[hol "cakeml/misc/miscScript.sml" "FOLDL_invariant_rest"
  (total_function_inhabitants := [α])]
theorem foldl_invariant_rest {α β : Type} [Nonempty α] (P : List α → β → Bool)
    (f : β → α → β) :
    ∀ (ls : List α) (a : β), P ls a = true ∧
      (∀ (x : β) (n : Nat), n < ls.length ∧ P (ls.drop n) x = true →
        P (ls.drop (n + 1)) (f x (holEl n ls)) = true) →
        P [] (ls.foldl f a) = true := by
  intro ls
  induction ls with
  | nil =>
    intro a h
    obtain ⟨hstart, _⟩ := h
    exact hstart
  | cons y ys ih =>
    intro a h
    obtain ⟨hstart, hstep⟩ := h
    simp only [List.foldl_cons]
    refine ih (f a y) ⟨?_, ?_⟩
    · have := hstep a 0 ⟨by simp, by simpa using hstart⟩
      simpa [holEl, holHd] using this
    · intro x n hn
      have hlen : n + 1 < (y :: ys).length := by
        simp only [List.length_cons]
        omega
      have := hstep x (n + 1) ⟨hlen, by simpa using hn.2⟩
      simpa [holEl_cons_succ] using this

end Flapjack
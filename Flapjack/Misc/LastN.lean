module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-!
# HOL `LASTN` length laws

Counterparts of `LASTN_LENGTH_LESS_EQ` and `LENGTH_LASTN_LESS` from
`cakeml/misc/miscScript.sml`. HOL's `rich_list$LASTN n xs` is
`REVERSE (TAKE n (REVERSE xs))`, rendered by the untagged
`Flapjack.wordSemLastN`.
-/

namespace Flapjack

/-- Original `LASTN_LENGTH_LESS_EQ`: taking the last `n` elements of a list no
longer than `n` keeps the whole list. -/
@[hol "cakeml/misc/miscScript.sml" "LASTN_LENGTH_LESS_EQ"]
theorem lastN_eq_self_of_length_le {α : Type} (xs : List α) (n : Nat)
    (h : xs.length ≤ n) : wordSemLastN n xs = xs := by
  unfold wordSemLastN
  rw [List.take_of_length_le (by simpa using h), List.reverse_reverse]

/-- Original `LENGTH_LASTN_LESS`: the last `n` elements are never longer than
the list. -/
@[hol "cakeml/misc/miscScript.sml" "LENGTH_LASTN_LESS"]
theorem length_lastN_le {α : Type} (xs : List α) (n : Nat) :
    (wordSemLastN n xs).length ≤ xs.length := by
  unfold wordSemLastN
  simp only [List.length_reverse, List.length_take]
  omega

/-- Original `LASTN_LEMMA`: the last elements of a list of length at most `n`
are the list itself, in both of HOL's shapes. -/
@[hol "cakeml/misc/miscScript.sml" "LASTN_LEMMA"]
theorem lastN_lemma {α : Type} (xs : List α) (x y : α) :
    wordSemLastN (xs.length + 1 + 1) (x :: y :: xs) = x :: y :: xs ∧
    wordSemLastN (xs.length + 1) (x :: xs) = x :: xs := by
  refine ⟨lastN_eq_self_of_length_le _ _ (by simp),
    lastN_eq_self_of_length_le _ _ (by simp)⟩

/-- Original `LASTN_TL`: the last `n+1` elements of a longer cons list ignore
the head. -/
@[hol "cakeml/misc/miscScript.sml" "LASTN_TL"]
theorem lastN_tl {α : Type} (n : Nat) (xs : List α) (x : α) (h : n < xs.length) :
    wordSemLastN (n + 1) (x :: xs) = wordSemLastN (n + 1) xs := by
  unfold wordSemLastN
  rw [List.reverse_cons,
    List.take_append_of_le_length (by
      simp only [List.length_reverse]
      omega)]

/-- Original `LASTN_ALT`: the last elements of the empty list are empty, and for
a cons list they are the whole list when it is short enough. -/
@[hol "cakeml/misc/miscScript.sml" "LASTN_ALT"]
theorem lastN_alt {α β : Type} (n : Nat) (x : β) (xs : List β) :
    wordSemLastN n ([] : List α) = [] ∧
    wordSemLastN n (x :: xs) =
      if (x :: xs).length ≤ n then x :: xs else wordSemLastN n xs := by
  constructor
  · simp [wordSemLastN]
  · by_cases h : (x :: xs).length ≤ n
    · rw [if_pos h]
      exact lastN_eq_self_of_length_le _ _ h
    · rw [if_neg h]
      unfold wordSemLastN
      rw [List.reverse_cons,
        List.take_append_of_le_length (by
          simp only [List.length_reverse] at ⊢
          simp only [List.length_cons] at h
          omega)]

end Flapjack

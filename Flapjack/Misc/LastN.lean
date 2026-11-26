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

end Flapjack

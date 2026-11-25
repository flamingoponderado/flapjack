module

public import Flapjack.HolRef

@[expose] public section

/-!
# Cake `mllist` auxiliary definitions

Lean counterparts of `intersperse_def` and the `LENGTH_AUX` counter from
`cakeml/basis/pure/mllistScript.sml:11-17` and `:567-580`, with the source
theorem `LENGTH_AUX_THM`.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `intersperse_def`: insert the separator between neighbouring
elements. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "intersperse_def"]
def intersperse {α : Type} (sep : α) : List α → List α
  | [] => []
  | [x] => [x]
  | x :: y :: xs => x :: sep :: intersperse sep (y :: xs)

/-- Original `LENGTH_AUX_def`: tail-recursive length with an accumulator. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "LENGTH_AUX_def"]
def lengthAux {α : Type} : List α → Nat → Nat
  | [], n => n
  | _ :: xs, n => lengthAux xs (n + 1)

/-- The auxiliary counter started at zero is the list length. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "LENGTH_AUX_THM"]
theorem length_eq_lengthAux {α : Type} (xs : List α) : xs.length = lengthAux xs 0 := by
  have general : ∀ n, lengthAux xs n = xs.length + n := by
    intro n
    induction xs generalizing n with
    | nil => simp [lengthAux]
    | cons x xs ih =>
      simp only [lengthAux]
      rw [ih]
      simp only [List.length_cons]
      omega
  rw [general]
  simp

end Flapjack.Basis.Pure.MlList

module

public import Flapjack.HolRef

@[expose] public section

/-!
# Cake `mllist` folds

Lean counterparts of `foldl_def`, `foldli_aux_def`, `foldli_def` and
`foldl_intro` in `cakeml/basis/pure/mllistScript.sml:443-483`.

`foldli_thm` is not ported: it states the result through HOL `FOLDRi`, which
has no decided Lean rendering.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `foldl_def`: fold from the left, element before accumulator. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "foldl_def"]
def foldl {α β : Type} (f : β → α → α) : α → List β → α
  | e, [] => e
  | e, h :: t => foldl f (f h e) t

/-- Original `foldli_aux_def`: left fold with an index counter. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "foldli_aux_def"]
def foldliAux {α β : Type} (f : Nat → β → α → α) : α → Nat → List β → α
  | e, _, [] => e
  | e, n, h :: t => foldliAux f (f n h e) (n + 1) t

/-- Original `foldli_def`: the indexed fold started at zero. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "foldli_def"]
def foldli {α β : Type} (f : Nat → β → α → α) (e : α) (l : List β) : α :=
  foldliAux f e 0 l

/-- Original `foldl_intro`: HOL `FOLDL` is `foldl` with flipped arguments. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "foldl_intro"]
theorem foldlIntro {α β : Type} (xs : List α) (x : β) (f : β → α → β) :
    List.foldl f x xs = foldl (fun x acc => f acc x) x xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons h t ih =>
      simp only [List.foldl, foldl]
      exact ih (f x h)

end Flapjack.Basis.Pure.MlList

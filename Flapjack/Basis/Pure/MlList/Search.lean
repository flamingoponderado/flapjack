module

public import Flapjack.HolRef

@[expose] public section

/-!
# Cake `mllist` list search

Lean counterparts of `index_find_thm` and `FIND_thm` in
`cakeml/basis/pure/mllistScript.sml:400-411`, together with renderings of the
HOL core `listTheory` definitions those statements use: `INDEX_FIND_def` and
`FIND_def`.  HOL's `OPTION_MAP SND` is `Option.map Prod.snd` and the boolean
predicate is a Lean `α → Bool`, so the equations keep HOL's shapes.
-/

namespace Flapjack.Basis.Pure.MlList

/-- HOL core `INDEX_FIND`: the first position whose element satisfies the
    predicate, paired with that element. -/
@[hol "HOL/src/list/src/listScript.sml" "INDEX_FIND_def"]
def holIndexFind {α : Type} (i : Nat) (p : α → Bool) : List α → Option (Nat × α)
  | [] => none
  | h :: t => if p h then some (i, h) else holIndexFind (i + 1) p t

/-- HOL core `FIND`: the first element satisfying the predicate. -/
@[hol "HOL/src/list/src/listScript.sml" "FIND_def"]
def holFind {α : Type} (p : α → Bool) (l : List α) : Option α :=
  (holIndexFind 0 p l).map Prod.snd

/-- Original `index_find_thm`: only the element of `INDEX_FIND` matters. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "index_find_thm"]
theorem holIndexFind_snd_independent {α : Type} (p : α → Bool) (l : List α) :
    ∀ x y : Nat,
      (holIndexFind x p l).map Prod.snd = (holIndexFind y p l).map Prod.snd := by
  induction l with
  | nil =>
    intro x y
    rfl
  | cons h t ih =>
    intro x y
    by_cases hp : p h
    · simp only [holIndexFind, hp, if_pos]
      rfl
    · simp only [holIndexFind, hp]
      exact ih (x + 1) (y + 1)

/-- Original `FIND_thm`: `FIND` satisfies HOL's two recursive equations. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "FIND_thm"]
theorem holFind_cons {α : Type} (p : α → Bool) :
    holFind p [] = none ∧
      ∀ h t, holFind p (h :: t) = if p h then some h else holFind p t := by
  refine ⟨rfl, ?_⟩
  intro h t
  by_cases hp : p h
  · simp only [holFind, holIndexFind, hp, if_pos]
    rfl
  · simp only [holFind, holIndexFind, hp]
    exact holIndexFind_snd_independent p t 1 0

/-- Original `INDEX_FIND_CONS_EQ_SOME` (`miscScript.sml`): the two ways the
first match of a nonempty list can be found. -/
@[hol "cakeml/misc/miscScript.sml" "INDEX_FIND_CONS_EQ_SOME"]
theorem holIndexFind_cons_eq_some {α : Type} (n : Nat) (f : α → Bool) (x : α)
    (xs : List α) (y : Nat × α) :
    (holIndexFind n f (x :: xs) = some y) ↔
      (f x = true ∧ y = (n, x)) ∨ (f x = false ∧ holIndexFind (n + 1) f xs = some y) := by
  cases hfx : f x with
  | true => simp [holIndexFind, hfx, eq_comm]
  | false => simp [holIndexFind, hfx]

/-- HOL `INDEX_OF`: the first position of `x`, via the equality predicate. -/
@[hol "HOL/src/list/src/listScript.sml" "INDEX_OF_def"]
def holIndexOf {α : Type} [DecidableEq α] (x : α) : List α → Option Nat :=
  (Option.map Prod.fst) ∘ (holIndexFind 0 (fun y => decide (y = x)))

end Flapjack.Basis.Pure.MlList

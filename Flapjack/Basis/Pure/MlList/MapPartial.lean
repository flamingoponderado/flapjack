module

public import Flapjack.HolRef
public import Flapjack.Misc.Option

@[expose] public section

/-!
# Cake `mllist` partial map

Lean counterparts of `mapPartial_def` and `mapPartial_thm` from
`cakeml/basis/pure/mllistScript.sml:387-395`. HOL's `THE` is the reviewed
`holThe` rendering, so the theorem carries the `total_function_inhabitants`
qualifier for its element type.
-/

namespace Flapjack.Basis.Pure.MlList

/-- Original `mapPartial_def`: map with an option-valued function, dropping
the undefined entries. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "mapPartial_def"]
def mapPartial {α β : Type} (f : α → Option β) : List α → List β
  | [] => []
  | h :: t =>
      match f h with
      | none => mapPartial f t
      | some x => x :: mapPartial f t

/-- The partial map is the total map, filtered to the defined entries and
projected with HOL's `THE`. -/
@[hol "cakeml/basis/pure/mllistScript.sml" "mapPartial_thm"
  (total_function_inhabitants := [β])]
theorem mapPartial_eq_mapThe_filter {α β : Type} [Nonempty β]
    (f : α → Option β) (l : List α) :
    mapPartial f l = ((l.map f).filter Option.isSome).map holThe := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [mapPartial]
    cases found : f h with
    | none =>
      rw [ih]
      simp [found]
    | some x =>
      rw [ih]
      simp [found, holThe]

end Flapjack.Basis.Pure.MlList

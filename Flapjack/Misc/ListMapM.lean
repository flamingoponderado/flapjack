/-! Shared `List.mapM` facts used by the executable compiler passes. -/

namespace Flapjack

/-- If every visited element maps to `f`, a successful `mapM` returns the
    pointwise image.

    This is Flapjack infrastructure with no HOL original: it is a generic list
    fact about `Option`-valued `mapM`, used to connect the executable passes'
    `mapM` traversals with the source-shaped `map` traversals. -/
theorem mapM_eq_map {α β : Type} (visit : α → Option β) (f : α → β)
    (correct : ∀ x y, visit x = some y → y = f x) (xs : List α) (ys : List β)
    (run : xs.mapM visit = some ys) : ys = xs.map f := by
  induction xs generalizing ys with
  | nil => simpa using run.symm
  | cons x rest ih =>
    simp only [List.mapM_cons] at run
    cases first : visit x with
    | none => simp [first] at run
    | some value =>
      cases remaining : rest.mapM visit with
      | none => simp [first, remaining] at run
      | some values =>
        simp [first, remaining] at run
        subst ys
        simp [correct x value first, ih values remaining]

end Flapjack

module

public import Flapjack.Misc.Sptree.Range
public import Flapjack.Misc.Sptree.Map

@[expose] public section

/-!
# Shape after mapping

Counterpart of `eq_shape_map` from `cakeml/misc/miscScript.sml`: mapping the
stored values does not change the branch shape, so `sptEqShape` is unchanged.
The `Sptree.Map` import lives here rather than in `Sptree/Range.lean`.
-/

namespace Flapjack

/-- Original `eq_shape_map`: mapping values does not change the shape. -/
@[hol "cakeml/misc/miscScript.sml" "eq_shape_map"]
theorem eqShapeMap {α β γ : Type} (t1 : Spt α) (t2 : Spt β) (f : α → γ) :
    sptEqShape (sptMap f t1) t2 = true ↔ sptEqShape t1 t2 = true := by
  induction t1 generalizing t2 with
  | ln =>
    cases t2 with
    | ln => rfl
    | ls _ => rfl
    | bn _ _ => rfl
    | bs _ _ _ => rfl
  | ls v =>
    cases t2 with
    | ln => rfl
    | ls _ => rfl
    | bn _ _ => rfl
    | bs _ _ _ => rfl
  | bn l r ihl ihr =>
    cases t2 with
    | ln => rfl
    | ls _ => rfl
    | bn l2 r2 => simp only [sptMap, sptEqShape, Bool.and_eq_true, ihl l2, ihr r2]
    | bs _ _ _ => rfl
  | bs l v r ihl ihr =>
    cases t2 with
    | ln => rfl
    | ls _ => rfl
    | bn _ _ => rfl
    | bs l2 _ r2 => simp only [sptMap, sptEqShape, Bool.and_eq_true, ihl l2, ihr r2]

end Flapjack

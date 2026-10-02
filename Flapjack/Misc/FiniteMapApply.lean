import Flapjack.Pancake.Semantics.CrepSem.HOLState

/-!
# HOL `FAPPLY` on the finite-support carrier

HOL `f ' x` (`FAPPLY_DEF`, `HOL/src/finite_maps/finite_mapScript.sml:174-176`)
is `OUTL (fmap_REP f x)`.  Outside `FDOM f` the representation is `INR one`, so
the value there is the single unspecified term `OUTL (INR one)` of the result
type: it depends on neither the map nor the key.  `holFapplyOutside` renders
that term as an opaque constant, so no Lean proof can fix its value.  This is
Flapjack infrastructure: the HOL declaration is outside the CakeML scripts and
the canonical carrier `HolFiniteMapExact` has no HOL counterpart of its own.
-/

namespace Flapjack

/-- HOL's unspecified `OUTL (INR one)` at result type `β`: the value of
`f ' x` for every `x ∉ FDOM f`. -/
noncomputable opaque holFapplyOutside (β : Type) [Nonempty β] : β

/-- HOL `FAPPLY` (`f ' x`) on the canonical finite-support carrier. -/
noncomputable def holFapply {α β : Type} [Nonempty β] (f : HolFiniteMapExact α β) (x : α) : β :=
  match f.lookup x with
  | some value => value
  | none => holFapplyOutside β

theorem holFapply_of_lookup {α β : Type} [Nonempty β] {f : HolFiniteMapExact α β} {x : α}
    {value : β} (h : f.lookup x = some value) : holFapply f x = value := by
  simp [holFapply, h]

end Flapjack

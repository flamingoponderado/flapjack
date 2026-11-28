module

public import Flapjack.HolRef
public import Mathlib.Logic.Relation

@[expose] public section

/-!
# HOL `RTC`, `RINTER` and `RSUBSET`

HOL's reflexive-transitive closure `RTC R x y` is rendered as Mathlib's
`Relation.ReflTransGen R x y`; `RINTER R1 R2` is the pointwise conjunction and
`RSUBSET R1 R2` the pointwise implication, both kept as the anonymous relations
they are in HOL. Counterparts of `RTC_invariant` and `RTC_RSUBSET` from
`cakeml/misc/miscScript.sml`.

The `Mathlib.Logic.Relation` import lives in this dedicated module so that it
does not change the simp set of the widely imported `Flapjack.Misc.Relation`.
-/

namespace Flapjack

/-- Original `RTC_invariant`: a predicate preserved by every step is preserved
along the reflexive-transitive closure, and the closure restricted to the
predicate still reaches the endpoint. -/
@[hol "cakeml/misc/miscScript.sml" "RTC_invariant"]
theorem rtcInvariant {α : Type} (R : α → α → Prop) (P : α → Prop)
    (hstep : ∀ x y, P x ∧ R x y → P y) :
    ∀ x y, Relation.ReflTransGen R x y → P x →
      Relation.ReflTransGen (fun x y => R x y ∧ P x ∧ P y) x y := by
  intro x y hrtc hP
  have hpy : ∀ {z}, Relation.ReflTransGen R x z → P z := by
    intro z hz
    induction hz with
    | refl => exact hP
    | tail _ hrel ih => exact hstep _ _ ⟨ih, hrel⟩
  induction hrtc with
  | refl => exact Relation.ReflTransGen.refl
  | tail hrtc hrel ih =>
    exact Relation.ReflTransGen.tail ih ⟨hrel, hpy hrtc, hstep _ _ ⟨hpy hrtc, hrel⟩⟩

/-- Original `RTC_RSUBSET`: a pointwise included relation has an included
reflexive-transitive closure. -/
@[hol "cakeml/misc/miscScript.sml" "RTC_RSUBSET"]
theorem rtcRsubset {α : Type} (R1 R2 : α → α → Prop) (hsub : ∀ x y, R1 x y → R2 x y) :
    ∀ x y, Relation.ReflTransGen R1 x y → Relation.ReflTransGen R2 x y := by
  intro x y hrtc
  induction hrtc with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hrel ih => exact Relation.ReflTransGen.tail ih (hsub _ _ hrel)

end Flapjack

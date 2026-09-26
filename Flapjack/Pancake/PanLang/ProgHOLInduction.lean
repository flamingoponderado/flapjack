import Flapjack.Pancake.PanLang.Prog

/-!
Lean-only well-founded induction support for the nested `ProgHOL` syntax.

This module has no HOL original: Cake's recursive Pan passes are HOL
definitions, but this theorem is a generic Lean proof principle for reasoning
about their `sizeOf`-recursive translations. In particular, unlike
`fun_induction` on a particular nested recursive definition, it gives an
induction hypothesis for every `ProgHOL` value with strictly smaller size.
-/

namespace Flapjack.Pancake.PanLang

/-- Strong induction over all smaller `ProgHOL` values, measured by Lean's
`sizeOf`. The unrestricted smaller-value hypothesis supports well-founded
functions whose recursive calls occur below nested `call` handler fields. -/
theorem progHOL_sizeOf_induction {width : Nat} [NeZero width]
    (motive : ProgHOL width → Prop)
    (step : ∀ program, (∀ smaller, sizeOf smaller < sizeOf program → motive smaller) →
      motive program) :
    ∀ program, motive program := by
  intro program
  exact Nat.strongRecOn (sizeOf program)
    (motive := fun bound => ∀ candidate : ProgHOL width,
      sizeOf candidate ≤ bound → motive candidate)
    (fun bound ih => by
      intro candidate hbound
      apply step candidate
      intro smaller hsmaller
      exact ih (sizeOf smaller) (by omega) smaller (Nat.le_refl _))
    program (Nat.le_refl _)

end Flapjack.Pancake.PanLang

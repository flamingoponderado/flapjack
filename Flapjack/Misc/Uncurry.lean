import Flapjack.HolRef

/-!
Exact port of HOL `misc$UNCURRY_eq_pair` (`cakeml/misc/miscScript.sml:2271`):

    Theorem UNCURRY_eq_pair:
      UNCURRY f v = z <=> ?a b. v = (a,b) /\ f a b = z

HOL's `UNCURRY` is `uncurry` (`UNCURRY f (a,b) = f a b`), rendered here by
composition-free `Function.uncurry`; `v` ranges over the product type
`α × β`, matching HOL `'a # 'b`.
-/

namespace Flapjack

@[hol "cakeml/misc/miscScript.sml" "UNCURRY_eq_pair"]
theorem uncurryEqPairHOL {α β γ : Type} (f : α → β → γ) (v : α × β) (z : γ) :
    Function.uncurry f v = z ↔ ∃ a b, v = (a, b) ∧ f a b = z := by
  constructor
  · intro h
    exact ⟨v.1, v.2, rfl, h⟩
  · rintro ⟨a, b, hv, h⟩
    subst hv
    exact h

end Flapjack

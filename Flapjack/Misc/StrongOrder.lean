module

public import Flapjack.Misc.Relation
public import Flapjack.Misc.Irreflexive

@[expose] public section

/-!
# HOL `antisymmetric`, `trichotomous`, `StrongOrder` and `StrongLinearOrder`

Exact ports of `HOL/src/relation/relationScript.sml`. As for `holTransitive`,
`holTotal` and `holIrreflexive`, HOL relations `'a -> 'a -> bool` are rendered
as `α → α → Prop`.
-/

namespace Flapjack

/-- Exact HOL `antisymmetric_def` (`relationScript.sml:47-49`):
`antisymmetric R = !x y. R x y /\ R y x ==> (x = y)`. -/
@[hol "HOL/src/relation/relationScript.sml" "antisymmetric_def"]
def holAntisymmetric {α : Type} (R : α → α → Prop) : Prop :=
  ∀ x y, R x y ∧ R y x → x = y

/-- Exact HOL `trichotomous` (`relationScript.sml:60-62`):
`trichotomous R = !a b. R a b \/ R b a \/ (a = b)`. -/
@[hol "HOL/src/relation/relationScript.sml" "trichotomous"]
def holTrichotomous {α : Type} (R : α → α → Prop) : Prop :=
  ∀ a b, R a b ∨ R b a ∨ a = b

/-- Exact HOL `StrongOrder` (`relationScript.sml:2148-2150`):
`StrongOrder R <=> irreflexive R /\ transitive R`. -/
@[hol "HOL/src/relation/relationScript.sml" "StrongOrder"]
def holStrongOrder {α : Type} (R : α → α → Prop) : Prop :=
  holIrreflexive R ∧ holTransitive R

/-- Exact HOL `StrongLinearOrder` (`relationScript.sml:2303-2305`):
`StrongLinearOrder R <=> StrongOrder R /\ trichotomous R`. -/
@[hol "HOL/src/relation/relationScript.sml" "StrongLinearOrder"]
def holStrongLinearOrder {α : Type} (R : α → α → Prop) : Prop :=
  holStrongOrder R ∧ holTrichotomous R

end Flapjack

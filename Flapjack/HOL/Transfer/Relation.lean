module

public import Flapjack.Misc.PredSet

@[expose] public section

/-!
# Transfer relations

Counterparts of `FUN_REL` (`HOL/src/quotient/src/quotientScript.sml`), the
`total`/`surj`/`bitotal` relation properties
(`HOL/src/transfer/transferScript.sml`) and the bounded quantifiers
`RES_FORALL`/`RES_EXISTS` (`HOL/src/bool/boolScript.sml`), over Prop-valued
relations and predicates.

This module sits outside the `Flapjack.HOL.Transfer.Fmsp` chain: it is imported
by the unify transfer-rule ports, not by the `Fmsp` conversion itself.
-/

namespace Flapjack.HOL.Transfer.Relation

/-- Original `FUN_REL`: the strong function relation `R1 ===> R2`, relating
functions pointwise under the argument and result relations. -/
@[hol "HOL/src/quotient/src/quotientScript.sml" "FUN_REL"]
def funRel {α β γ δ : Type} (r1 : α → β → Prop) (r2 : γ → δ → Prop)
    (f : α → γ) (g : β → δ) : Prop :=
  ∀ x y, r1 x y → r2 (f x) (g y)

/-- Original `total`: every left element relates to some right element. -/
@[hol "HOL/src/transfer/transferScript.sml" "total_def"]
def total {α β : Type} (r : α → β → Prop) : Prop := ∀ x, ∃ y, r x y

/-- Original `surj`: every right element is related from some left element. -/
@[hol "HOL/src/transfer/transferScript.sml" "surj_def"]
def surj {α β : Type} (r : α → β → Prop) : Prop := ∀ y, ∃ x, r x y

/-- Original `bitotal`: the relation is both total and surjective. -/
@[hol "HOL/src/transfer/transferScript.sml" "bitotal_def"]
def bitotal {α β : Type} (r : α → β → Prop) : Prop := total r ∧ surj r

/-- Original `RES_FORALL_DEF`: the bounded universal quantifier. -/
@[hol "HOL/src/bool/boolScript.sml" "RES_FORALL_DEF"]
def resForall {α : Type} (p : α → Prop) (m : α → Prop) : Prop := ∀ x, p x → m x

/-- Original `RES_EXISTS_DEF`: the bounded existential quantifier. -/
@[hol "HOL/src/bool/boolScript.sml" "RES_EXISTS_DEF"]
def resExists {α : Type} (p : α → Prop) (m : α → Prop) : Prop := ∃ x, p x ∧ m x

end Flapjack.HOL.Transfer.Relation

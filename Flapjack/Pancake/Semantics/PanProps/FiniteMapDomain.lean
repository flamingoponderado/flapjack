module

public import Flapjack.FiniteMap.DomainExact
public import Flapjack.Pancake.Semantics.PanProps

@[expose] public section

/-!
# panProps finite-map domain lemmas

Exact ports of the `panPropsScript.sml` theorems that reason about `FDOM`
through the canonical `HolFiniteMapExact.domain` key set. This is a leaf
module on purpose: `Flapjack/FiniteMap/DomainExact.lean` imports the Mathlib
set library, and pulling that into `PanProps.lean` itself would change the
simp set visible to every downstream proof, so the hub stays free of it and
nothing imports this module except the umbrella.
-/

namespace Flapjack

/-- Exact HOL `fdoms_eq_flookup_some_none` (`panPropsScript.sml:276`): equal
    domains and a binding of `fm` at `n` give a binding of `fm'` at `n`. HOL
    also quantifies a vacuous `v' : δ` that occurs nowhere in the statement, so
    it is omitted here; the two maps keep HOL's independent value types, `FDOM`
    is the canonical key set and `FLOOKUP` is `.lookup`. -/
@[hol "cakeml/pancake/semantics/panPropsScript.sml" "fdoms_eq_flookup_some_none"
  (fmap_as_finite_support_relation := [fm, fm'])]
theorem fdomsEqFlookupSomeNoneExact {α β γ : Type} (fm : HolFiniteMapExact α β)
    (fm' : HolFiniteMapExact α γ) (n : α) (v : β) :
    fm.domain = fm'.domain ∧ fm.lookup n = some v → ∃ v' : γ, fm'.lookup n = some v' := by
  rintro ⟨hdom, hlookup⟩
  have hmem : fm'.lookup n ≠ none := by
    have hpoint : fm.domain n = fm'.domain n := congrFun hdom n
    change (fm.lookup n ≠ none) = (fm'.lookup n ≠ none) at hpoint
    rw [← hpoint]
    simp [hlookup]
  exact Option.isSome_iff_exists.mp ((Option.ne_none_iff_isSome (o := fm'.lookup n)).mp hmem)

end Flapjack

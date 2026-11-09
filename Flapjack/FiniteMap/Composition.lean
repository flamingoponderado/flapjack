module

public import Flapjack.Misc.FiniteMapApply

@[expose] public section

/-! Composition for canonical finite-support maps. -/
namespace Flapjack.HolFiniteMapExact

/-- Compose finite maps using successful lookup in both maps. This Flapjack
infrastructure follows HOL finite-map composition's domain and lookup rules;
it is not itself a tagged port of HOL's specification declaration. -/
def compose {α β γ : Type} (outer : HolFiniteMapExact β γ) (inner : HolFiniteMapExact α β) :
    HolFiniteMapExact α γ where
  lookup key := (inner.lookup key).bind outer.lookup
  finiteSupport := by
    obtain ⟨keys, support⟩ := inner.finiteSupport
    refine ⟨keys, ?_⟩
    intro key present
    apply support key
    intro empty
    simp [empty] at present

/-- A composed lookup succeeds exactly when both constituent lookups do. -/
theorem lookup_compose_some {α β γ : Type} (outer : HolFiniteMapExact β γ)
    (inner : HolFiniteMapExact α β) (key : α) (value : γ) :
    (compose outer inner).lookup key = some value ↔
      ∃ intermediate, inner.lookup key = some intermediate ∧ outer.lookup intermediate = some value := by
  cases found : inner.lookup key <;> simp [compose, found]

/-- An existing pair of lookup results determines a composed lookup. -/
theorem lookup_compose_of_lookup {α β γ : Type} (outer : HolFiniteMapExact β γ)
    (inner : HolFiniteMapExact α β) (key : α) (intermediate : β) (value : γ)
    (first : inner.lookup key = some intermediate) (second : outer.lookup intermediate = some value) :
    (compose outer inner).lookup key = some value := by
  simp [compose, first, second]

/-- Total HOL map application agrees with composition on a defined path. -/
theorem apply_compose_of_lookup {α β γ : Type} [Nonempty β] [Nonempty γ]
    (outer : HolFiniteMapExact β γ) (inner : HolFiniteMapExact α β) (key : α)
    (intermediate : β) (value : γ)
    (first : inner.lookup key = some intermediate) (second : outer.lookup intermediate = some value) :
    holFapply (compose outer inner) key = holFapply outer (holFapply inner key) := by
  rw [holFapply_of_lookup (lookup_compose_of_lookup outer inner key intermediate value first second),
    holFapply_of_lookup first, holFapply_of_lookup second]

end Flapjack.HolFiniteMapExact

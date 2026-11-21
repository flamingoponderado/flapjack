module

public import Flapjack.Misc.FiniteMapApply
public import Flapjack.FiniteMap.DomainExact

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-! Composition for canonical finite-support maps. -/
namespace Flapjack.HolFiniteMapExact

/-- The constant introduced by HOL's `f_o_f_DEF` specification
(`f f_o_f g`, here `compose f g`), using the canonical finite-support
carrier: a key is defined when the inner lookup succeeds and the outer lookup
of its image succeeds. The accompanying `compose_spec` proves the whole
specification, which determines the map by domain and lookup extensionality. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "f_o_f_DEF" (fmap_as_finite_support_result)]
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

/-- Independent lookup-level composition for the finite-support codec witness. -/
def composeRaw {α β γ : Type} (outer : β → Option γ) (inner : α → Option β) (key : α) : Option γ :=
  match inner key with
  | none => none
  | some middle => outer middle

/-- The canonical composition agrees with raw lookup composition. -/
theorem holFmapAsFiniteSupportResultWitness_compose {α β γ : Type}
    (outer : HolFiniteMapExact β γ) (inner : HolFiniteMapExact α β) (key : α) :
    (compose outer inner).lookup key = composeRaw outer.lookup inner.lookup key := by
  cases h : inner.lookup key <;> simp [compose, composeRaw, h]

open Classical in
/-- The theorem returned by HOL's `f_o_f_DEF` specification: the composed
domain is the inner domain restricted to keys whose image lies in the outer
domain, and the composed map applies the outer map to the inner image. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "f_o_f_DEF"
  (fmap_as_finite_support_parameters := [f, g])
  (total_function_inhabitants := [β, γ])]
theorem compose_spec {α β γ : Type} [Nonempty β] [Nonempty γ]
    (f : HolFiniteMapExact β γ) (g : HolFiniteMapExact α β) :
    (compose f g).domain = g.domain ∩ {x | holFapply g x ∈ f.domain} ∧
      ∀ x, x ∈ (compose f g).domain → holFapply (compose f g) x = holFapply f (holFapply g x) := by
  constructor
  · ext x
    change (compose f g).lookup x ≠ none ↔ g.lookup x ≠ none ∧ f.lookup (holFapply g x) ≠ none
    cases hg : g.lookup x with
    | none => simp [compose, hg]
    | some middle =>
      rw [holFapply_of_lookup hg]
      simp [compose, hg]
  · intro x member
    change (compose f g).lookup x ≠ none at member
    cases hg : g.lookup x with
    | none => simp [compose, hg] at member
    | some middle =>
      cases hf : f.lookup middle with
      | none => simp [compose, hg, hf] at member
      | some value =>
        rw [holFapply_of_lookup hg, holFapply_of_lookup hf,
          holFapply_of_lookup (show (compose f g).lookup x = some value by simp [compose, hg, hf])]

/-- Forget the finite-support certificate of a map argument. -/
private def toBroad {α β : Type} (map : HolFiniteMapExact α β) := map.lookup

/-- Rebuild a map argument from its lookup and finite-support certificate. -/
private def ofBroad {α β : Type} (lookup : α → Option β)
    (finite : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact α β := ⟨lookup, finite⟩

/-- The outer map argument has the canonical lookup/support codec. -/
theorem holFmapAsFiniteSupportParamWitness_compose_spec_f {β γ : Type}
    (f : HolFiniteMapExact β γ) (key : β) :
    (ofBroad (toBroad f) f.finiteSupport).lookup key = f.lookup key ∧
    (ofBroad (toBroad f) f.finiteSupport).finiteSupport = f.finiteSupport ∧
    ofBroad (toBroad f) f.finiteSupport = f := by
  cases f
  exact ⟨rfl, rfl, rfl⟩

/-- The inner map argument has the canonical lookup/support codec. -/
theorem holFmapAsFiniteSupportParamWitness_compose_spec_g {α β : Type}
    (g : HolFiniteMapExact α β) (key : α) :
    (ofBroad (toBroad g) g.finiteSupport).lookup key = g.lookup key ∧
    (ofBroad (toBroad g) g.finiteSupport).finiteSupport = g.finiteSupport ∧
    ofBroad (toBroad g) g.finiteSupport = g :=
  holFmapAsFiniteSupportParamWitness_compose_spec_f g key

end Flapjack.HolFiniteMapExact

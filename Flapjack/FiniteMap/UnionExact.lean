module

public import Flapjack.Pancake.Semantics.CrepSem.HOLState
public import Flapjack.FiniteMap.DomainExact
public import Flapjack.Misc.FiniteMapApply

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Flapjack.HolFiniteMapExact

/-- The constant introduced by HOL's `FUNION_DEF` specification, using the
canonical finite-support carrier. The accompanying `union_spec` proves the
whole specification, which determines the map by domain and lookup extensionality. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_DEF" (fmap_as_finite_support_result)]
def union (left right : HolFiniteMapExact α β) : HolFiniteMapExact α β where
  lookup key := match left.lookup key with
    | none => right.lookup key
    | some value => some value
  finiteSupport := by
    obtain ⟨leftKeys, hleft⟩ := left.finiteSupport
    obtain ⟨rightKeys, hright⟩ := right.finiteSupport
    refine ⟨leftKeys ++ rightKeys, ?_⟩
    intro key h
    cases hl : left.lookup key with
    | none =>
      exact List.mem_append.mpr (Or.inr (hright key (by simpa [hl] using h)))
    | some value =>
      exact List.mem_append.mpr (Or.inl (hleft key (by simp [hl])))

/-- Independent lookup-level union for the finite-support codec witness. -/
def unionRaw (left right : α → Option β) (key : α) : Option β :=
  match left key with
  | none => right key
  | some value => some value

/-- The canonical union agrees with raw left-biased lookup. -/
theorem holFmapAsFiniteSupportResultWitness_union
    (left right : HolFiniteMapExact α β) (key : α) :
    (union left right).lookup key = unionRaw left.lookup right.lookup key := rfl

/-- Unconditional observation law for the carrier extension, not a separately
qualified port of HOL's theorem over its abstract finite-map carrier. -/
@[simp] theorem lookup_union (left right : HolFiniteMapExact α β) (key : α) :
    (left.union right).lookup key =
      match left.lookup key with
      | none => right.lookup key
      | some value => some value := rfl

/-- The union domain is exactly the union of the two defined lookup domains;
this infrastructure theorem assumes neither domain containment nor disjointness. -/
theorem union_defined_iff (left right : HolFiniteMapExact α β) (key : α) :
    (left.union right).lookup key ≠ none ↔
      left.lookup key ≠ none ∨ right.lookup key ≠ none := by
  cases hl : left.lookup key <;> simp [lookup_union, hl]

open Classical in
/-- The theorem returned by HOL's `FUNION_DEF` specification. -/
@[hol "HOL/src/finite_maps/finite_mapScript.sml" "FUNION_DEF"
  (fmap_as_finite_support_parameters := [left, right])]
theorem union_spec {α β : Type} [Nonempty β]
    (left : HolFiniteMapExact α β) (right : HolFiniteMapExact α β) :
    (left.union right).domain = left.domain ∪ right.domain ∧
      ∀ x, holFapply (left.union right) x =
        if x ∈ left.domain then holFapply left x else holFapply right x := by
  constructor
  · ext x
    exact union_defined_iff left right x
  · intro x
    have domainEq : (x ∈ left.domain) ↔ left.lookup x ≠ none := Iff.rfl
    simp only [domainEq]
    cases h : left.lookup x <;> simp [holFapply, lookup_union, h]

private def toBroad (map : HolFiniteMapExact α β) := map.lookup

private def ofBroad (lookup : α → Option β)
    (finite : ∃ keys : List α, ∀ key, lookup key ≠ none → key ∈ keys) :
    HolFiniteMapExact α β := ⟨lookup, finite⟩

/-- The first map argument has the canonical lookup/support codec. -/
theorem holFmapAsFiniteSupportParamWitness_union_spec_left
    (left : HolFiniteMapExact α β) (key : α) :
    (ofBroad (toBroad left) left.finiteSupport).lookup key = left.lookup key ∧
    (ofBroad (toBroad left) left.finiteSupport).finiteSupport = left.finiteSupport ∧
    ofBroad (toBroad left) left.finiteSupport = left := by
  cases left
  exact ⟨rfl, rfl, rfl⟩

/-- The second map argument has the canonical lookup/support codec. -/
theorem holFmapAsFiniteSupportParamWitness_union_spec_right
    (right : HolFiniteMapExact α β) (key : α) :
    (ofBroad (toBroad right) right.finiteSupport).lookup key = right.lookup key ∧
    (ofBroad (toBroad right) right.finiteSupport).finiteSupport = right.finiteSupport ∧
    ofBroad (toBroad right) right.finiteSupport = right :=
  holFmapAsFiniteSupportParamWitness_union_spec_left right key

end Flapjack.HolFiniteMapExact

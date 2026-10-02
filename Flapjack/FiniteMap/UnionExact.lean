import Flapjack.Pancake.Semantics.CrepSem.HOLState

namespace Flapjack.HolFiniteMapExact

/-- Canonical finite-support carrier infrastructure for HOL's left-biased
`FUNION`. There is no separate HOL declaration for this Lean carrier extension,
so it is untagged. The lookup equation follows `FLOOKUP_FUNION`; retaining
finite support makes it usable by the faithful balanced-map semantic map.
No key equality decision or comparator law is required. -/
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

end Flapjack.HolFiniteMapExact

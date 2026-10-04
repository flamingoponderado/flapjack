import Flapjack.Misc.SetSep

/-! `miscScript.sml` `fun2set_disjoint_union`: separation over the graph of one
memory on a disjoint union of domains. Sets are predicates, as in the reviewed
set_sep port. -/
namespace Flapjack.Misc.Fun2SetUnion
open Flapjack.SetSep

/-- Full original `fun2set_disjoint_union` (`miscScript.sml:4262-4274`):
`DISJOINT d1 d2 ∧ p (fun2set (m,d1)) ∧ q (fun2set (m,d2)) ⇒
(p * q) (fun2set (m, d1 ∪ d2))`, for arbitrary address/value types; HOL
`DISJOINT` is pointwise non-overlap and `∪` the pointwise disjunction. -/
@[hol "cakeml/misc/miscScript.sml" "fun2set_disjoint_union"]
theorem fun2SetDisjointUnion {α β : Type} (d1 d2 : α → Prop) (m : α → β)
    (p q : ((α × β) → Prop) → Prop)
    (h : (∀ x, ¬ (d1 x ∧ d2 x)) ∧ p (fun2Set (m, d1)) ∧ q (fun2Set (m, d2))) :
    star p q (fun2Set (m, fun x => d1 x ∨ d2 x)) := by
  obtain ⟨disjoint, hp, hq⟩ := h
  refine ⟨fun2Set (m, d1), fun2Set (m, d2), ⟨?_, ?_⟩, hp, hq⟩
  · funext ⟨a, v⟩
    apply propext
    constructor
    · rintro (⟨x, hx, e⟩ | ⟨x, hx, e⟩)
      · exact ⟨x, Or.inl hx, e⟩
      · exact ⟨x, Or.inr hx, e⟩
    · rintro ⟨x, hx | hx, e⟩
      · exact Or.inl ⟨x, hx, e⟩
      · exact Or.inr ⟨x, hx, e⟩
  · rintro ⟨a, v⟩ ⟨⟨x, hx, e⟩, ⟨y, hy, e'⟩⟩
    have hxa : a = x := congrArg Prod.fst e
    have hya : a = y := congrArg Prod.fst e'
    subst hxa; subst hya
    exact disjoint a ⟨hx, hy⟩

end Flapjack.Misc.Fun2SetUnion

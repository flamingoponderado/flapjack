import Flapjack.HolRef
import Flapjack.Misc.ListEl
import Mathlib.Data.List.Forall2

/-! List-relation prerequisite for flat-to-closure correctness. -/
namespace Flapjack.Compiler.Backend.FlatToClos

/-- Pointwise list relation characterized by equal lengths and bounded HOL
element lookup. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "LIST_REL_EL"]
theorem listRel_el {α β : Type} [Nonempty α] [Nonempty β]
    (xs : List α) (ys : List β) (r : α → β → Prop) :
    List.Forall₂ r xs ys ↔ xs.length = ys.length ∧
      ∀ n, n < ys.length → r (Flapjack.holEl n xs) (Flapjack.holEl n ys) := by
  rw [List.forall₂_iff_get]
  constructor
  · rintro ⟨length, related⟩
    refine ⟨length, ?_⟩
    intro n bound
    have leftBound : n < xs.length := by simpa [length] using bound
    simpa only [List.get_eq_getElem, Flapjack.holEl_eq_getElem n xs leftBound,
      Flapjack.holEl_eq_getElem n ys bound] using related n leftBound bound
  · rintro ⟨length, related⟩
    refine ⟨length, ?_⟩
    intro n leftBound rightBound
    simpa only [List.get_eq_getElem, Flapjack.holEl_eq_getElem n xs leftBound,
      Flapjack.holEl_eq_getElem n ys rightBound] using related n rightBound

end Flapjack.Compiler.Backend.FlatToClos

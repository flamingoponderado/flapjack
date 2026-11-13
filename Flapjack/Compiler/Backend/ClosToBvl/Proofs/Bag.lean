module

public import Flapjack.Misc.Bag

@[expose] public section

/-! Bag facts used by the closure-to-BVL oracle proof. -/
namespace Flapjack.Compiler.Backend.ClosToBvl

/-- Bag union is monotone in both operands. -/
@[hol "cakeml/compiler/backend/proofs/clos_to_bvlProofScript.sml" "BAG_UNION_MONO"]
theorem bagUnion_mono {α : Type} (a b c d : Flapjack.Bag α)
    (h : Flapjack.subBag a b ∧ Flapjack.subBag c d) :
    Flapjack.subBag (Flapjack.bagUnion a c) (Flapjack.bagUnion b d) := by
  intro x n bound
  have left := h.1 x (a x) (Nat.le_refl _)
  have right := h.2 x (c x) (Nat.le_refl _)
  exact Nat.le_trans bound (Nat.add_le_add left right)

end Flapjack.Compiler.Backend.ClosToBvl

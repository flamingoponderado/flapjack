import Flapjack.Compiler.Backend.Bvi.GeneratedSize
import Flapjack.HolRef

/-! List properties of the original generated BVI size. -/
namespace Flapjack.Compiler.Backend.BviLet.Proofs

/-- The HOL-generated size of an append is the sum of its list sizes. -/
@[hol "cakeml/compiler/backend/proofs/bvi_letProofScript.sml" "exp_size_APPEND"]
theorem expSize_append (xs ys : List Bvi.Exp) :
    Bvi.expListSizeHOL (xs ++ ys) = Bvi.expListSizeHOL xs + Bvi.expListSizeHOL ys := by
  induction xs with
  | nil => simp [Bvi.expListSizeHOL]
  | cons x xs ih => simp [Bvi.expListSizeHOL, ih, Nat.add_assoc]

end Flapjack.Compiler.Backend.BviLet.Proofs

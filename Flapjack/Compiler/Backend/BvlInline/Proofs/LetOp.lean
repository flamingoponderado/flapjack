import Flapjack.Compiler.Backend.BvlInline.LetOp
import Flapjack.Misc.ListEl

/-! Structural properties of the BVL let-operation traversal. -/
namespace Flapjack.Compiler.Backend.BvlInline.Proofs
open Bvl

/-- The source list traversal preserves the number of expressions. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "LENGTH_let_op"]
theorem lengthLetOp (expressions : List Exp) : (letOp expressions).length = expressions.length := by
  induction expressions with
  | nil => simp [letOp, letOpList]
  | cons head tail ih => simpa [letOp, letOpList] using ih

/-- A singleton result is exactly the singleton containing its HOL head. -/
@[hol "cakeml/compiler/backend/proofs/bvl_inlineProofScript.sml" "HD_let_op"]
theorem headLetOp (expression : Exp) :
    [@Flapjack.holHd Exp ⟨.var 0⟩ (letOp [expression])] = letOp [expression] := by
  simp [letOp, letOpList, Flapjack.holHd]

end Flapjack.Compiler.Backend.BvlInline.Proofs

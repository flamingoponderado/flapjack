import Flapjack.Pancake.LoopLang
import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

/-!
# loop_call `is_load_def`

Exact port of `cakeml/pancake/loop_callScript.sml`'s `is_load_def` (10-15) over
`WordMemOp`, the `memop` carrier of the tagged `HolLoopProg.shMem` (bead
`flapjack-pxn.18.5.7.3.1`).
-/

namespace Flapjack

/-- Exact HOL `loop_call$is_load_def` (`loop_callScript.sml:10-15`):
    `is_load Load = T ∧ is_load Load8 = T ∧ is_load Load16 = T ∧ is_load Load32 = T ∧
      is_load _ = F`. -/
@[hol "cakeml/pancake/loop_callScript.sml" "is_load_def"]
def loopCallIsLoadHOL : WordMemOp → Bool
  | .load => true
  | .load8 => true
  | .load16 => true
  | .load32 => true
  | _ => false

/-- The tagged `is_load` agrees with the evaluator's untagged `crepIsLoadMemOp`. -/
theorem loopCallIsLoadHOL_eq_crepIsLoadMemOp :
    loopCallIsLoadHOL = crepIsLoadMemOp := by
  funext op; cases op <;> rfl

end Flapjack

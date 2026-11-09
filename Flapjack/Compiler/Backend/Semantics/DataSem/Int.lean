module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Value
public import Flapjack.Compiler.Backend.BackendCommon.SmallInt

@[expose] public section

/-! Integer primitives of the data-language semantics. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack.Compiler.Backend.BackendCommon

/-- Integer operations with the original constant bound, floor division,
remainder, and bounded small-constant comparison. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_int_app_def"]
def doIntApp : ClosLang.IntOp → List Value → Option Value
  | .const n, [] => if smallEnoughInt n then some (.number n) else none
  | .add, [.number a, .number b] => some (.number (a + b))
  | .sub, [.number a, .number b] => some (.number (a - b))
  | .mult, [.number a, .number b] => some (.number (a * b))
  | .div, [.number a, .number b] => if b = 0 then none else some (.number (a.fdiv b))
  | .mod, [.number a, .number b] => if b = 0 then none else some (.number (a.fmod b))
  | .less, [.number a, .number b] => some (boolValue (decide (a < b)))
  | .lessEq, [.number a, .number b] => some (boolValue (decide (a ≤ b)))
  | .greater, [.number a, .number b] => some (boolValue (decide (a > b)))
  | .greaterEq, [.number a, .number b] => some (boolValue (decide (a ≥ b)))
  | .lessConstSmall n, [.number i] =>
      if 0 ≤ i ∧ i ≤ 1000000 ∧ n < 1000000 then some (boolValue (decide (i < Int.ofNat n))) else none
  | _, _ => none

end Flapjack.Compiler.Backend.DataSem

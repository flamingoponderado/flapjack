import Flapjack.Compiler.Backend.Semantics.BvlSem.Value

/-! BVL integer primitives. -/
namespace Flapjack.Compiler.Backend.BvlSem

/-- Original integer operations, with floor division and remainder and the
source's bounded small-constant comparison. -/
@[hol "cakeml/compiler/backend/semantics/bvlSemScript.sml" "do_int_app_def"]
def doIntApp : ClosLang.IntOp → List Value → Option Value
  | .const n, [] => some (.number n)
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
    if 0 ≤ i ∧ i ≤ 1000000 ∧ n < 1000000 then
      some (boolValue (decide (i < Int.ofNat n))) else none
  | _, _ => none

end Flapjack.Compiler.Backend.BvlSem

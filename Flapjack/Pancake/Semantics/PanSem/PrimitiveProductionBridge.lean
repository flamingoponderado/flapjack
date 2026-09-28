import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Pancake.Semantics.PanSem.Primop
import Flapjack.Pancake.Semantics.PanSem.TotalEvalExpBridge
import Flapjack.Pancake.Semantics.PanSem.ValueHOL

/-!
# Concrete production primitive wiring for state-based PanSem

The generic state evaluator accepts a `PanPrimitiveHandler` so proofs and
clients can state explicit contracts. This module adds the concrete 64-bit
source-state entry point that runs the reviewed production `panPrimopHOL`.
That handler is a String/PanValue analogue rather than a direct HOL definition;
the exact definition is `panPrimopHOLExact` and no HOL tag is claimed for the
runner. `TotalEvalExpBridge` records the production/exact handler relation and
its byte-rangedness proof.
-/

namespace Flapjack

/-- State-based production source evaluation with its concrete AddCarry
    primitive handler fixed to `panPrimopHOL`. -/
def panSemEvaluateRiscV64CodeStateWithProductionPrimop [NeZero 64]
    [BEq (RiscV.Word 64)] [OfNat (RiscV.Word 64) 0]
    [OfNat (RiscV.Word 64) 1] [OfNat (RiscV.Word 64) 2]
    [OfNat (RiscV.Word 64) 3] [Add (RiscV.Word 64)]
    [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (context : PanValueFfiContext (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (program : Prog (RiscV.Word 64)) :
    Option (PanValueFfiClockResult (RiscV.Word 64) σ) :=
  panSemEvaluateRiscV64CodeState context panPrimopHOL handler state program

/-- The concrete runner is the generic source-state evaluator with exactly the
    fixed production handler; its original parameterized interface is retained
    for explicit-handler proofs. -/
theorem panSemEvaluateRiscV64CodeStateWithProductionPrimop_eq
    [NeZero 64] [BEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)]
    [Sub (RiscV.Word 64)] [AndOp (RiscV.Word 64)]
    [OrOp (RiscV.Word 64)] [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)]
    (context : PanValueFfiContext (RiscV.Word 64))
    (handler : PanValueStatefulFfiHandler (RiscV.Word 64) σ)
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (program : Prog (RiscV.Word 64)) :
    panSemEvaluateRiscV64CodeStateWithProductionPrimop context handler state program =
      panSemEvaluateRiscV64CodeState context panPrimopHOL handler state program := rfl

end Flapjack

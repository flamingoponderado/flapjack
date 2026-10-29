import Flapjack.Compiler.Backend.ClosInterp.Proofs.EvaluateBasic

/-! Correctness of the interpreter's environment lookup helper. Its evaluator
and value carriers remain proof-side and await cross-language review. -/
namespace Flapjack.Compiler.Backend.ClosInterp

/-- Looking up index zero returns the first encoded environment element. -/
theorem evaluate_closInterpEl_zero {C F : Type} (first : ClosSem.Value) (tail : List ClosSem.Value)
    (recursive : ClosSem.Value) (rest : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [closInterpEl]
      (ClosSem.listToValue (first :: tail) :: .number 0 :: recursive :: rest) state =
        (.val [first], state) := by
  change ClosSem.evaluate [
      .ifThenElse .none (.op .none (.blockOp (.equalConst (.int 0))) [.var .none 1])
        (.op .none (.blockOp (.elemAt 0)) [.var .none 0])
        (.app .none none (.app .none none (.var .none 2)
          [.op .none (.intOp .sub) [.op .none (.intOp (.const 1)) [], .var .none 1]])
          [.op .none (.blockOp (.elemAt 1)) [.var .none 0]])]
      (ClosSem.listToValue (first :: tail) :: .number 0 :: recursive :: rest) state = _
  simp [ClosSem.listToValue, ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp,
    ClosSem.applyBlock, ClosSem.asBool, ClosSem.boolValue, BackendCommon.trueTag]

end Flapjack.Compiler.Backend.ClosInterp

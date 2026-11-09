import Flapjack.Compiler.Backend.FlatToClos.Proofs.ByteConversion

/-! Integer-to-character conversion for flat-to-closure lowering. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- The emitted bounds checks agree with the source conversion, including
its character exception. -/
theorem intToChar_body_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (env : List ClosSem.Value) (value : Int)
    (states : StateRel source target) :
    let flat := FlatSem.applyResult source (.src (.fromTo .intT .charT)) [.litv (.intLit value)]
    let clos := ClosSem.evaluate
      [.ifThenElse trace (.op trace (.intOp .less)
        [.op .none (.intOp (.const 0)) [], .var trace 0])
        (.raise trace (.op trace (.blockOp (.cons 1)) []))
        (.ifThenElse trace (.op trace (.intOp .less)
          [.var trace 0, .op .none (.intOp (.const 255)) []])
          (.raise trace (.op trace (.blockOp (.cons 1)) [])) (.var trace 0))]
      (.number value :: env) target
    StateRel flat.1 clos.2 ∧ EvalResultRel flat.2 clos.1 := by
  by_cases low : value < 0 <;> by_cases high : 255 < value
  all_goals simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.applyNumericProjection,
    FlatSem.flatToValue, FlatSem.valueToFlat, SemanticPrimitivesHOL.doApp_fromTo_core, SemanticPrimitivesHOL.doAppNumericCore,
    ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyBlock, ClosSem.applyNumeric, ClosSem.doIntApp,
    ClosSem.boolValue, ClosSem.asBool, BackendCommon.trueTag, BackendCommon.falseTag, low, high, states]
  all_goals first | exact .raise (.con .nil) | skip
  have nonnegative : 0 ≤ value := by omega
  have inRange : value.toNat < 256 := by omega
  have related := ValueRel.char (BitVec.ofNat 8 value.toNat)
  have finalRel : ValueRel (.litv (.char (BitVec.ofNat 8 value.toNat))) (.number value) := by
    simpa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt inRange, Int.toNat_of_nonneg nonnegative] using related
  exact .value (.cons finalRel .nil)

end Flapjack.Compiler.Backend.FlatToClos

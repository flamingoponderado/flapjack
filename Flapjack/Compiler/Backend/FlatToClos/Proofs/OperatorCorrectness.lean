import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.FlatToClos.Op
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateExact
import Flapjack.SemanticPrimitivesProps.ResultRelation
import Flapjack.EvaluateHOL
import Mathlib.Data.List.Forall2

namespace Flapjack.Compiler.Backend.FlatToClos

open Flapjack.SemanticPrimitivesHOL

namespace OperatorCorrectness
/-- The closure-state finite maps roundtrip through their broad carrier. -/
theorem holFmapAsFiniteSupportWitness {C F : Type} :
    (∀ s : ClosSem.StateBroad C F, (ClosSem.State.ofBroad s).toBroad = s) ∧
    (∀ s : ClosSem.State C F, ClosSem.State.ofBroad s.toBroad = s) :=
  ClosSem.holFmapAsFiniteSupportWitness
end OperatorCorrectness

/-- The original Eval operator case of value-level operator correctness.
The flat primitive dispatcher handles Eval in the evaluator rather than
`doApp`, so the original successful-application premise is impossible. -/
@[hol "cakeml/compiler/backend/proofs/flat_to_closProofScript.sml" "op_eval"
  (fmap_as_finite_support := [refs, code])]
theorem opEval {C F : Type} (op : FlatLang.Op) (source : FlatSem.State C F)
    (vs : List FlatSem.Value) (sourceNext : FlatSem.State C F)
    (result : Result FlatSem.Value FlatSem.Value) (targetNext : ClosSem.State C F)
    (xs : List ClosLang.Exp) (db : List ClosSem.Value) (target : ClosSem.State C F)
    (ws : List ClosSem.Value) (trace : BackendCommon.Tra) :
    op = .src .eval →
    FlatSem.doApp source op vs = some (sourceNext, result) ∧
      StateRel source targetNext ∧ ClosSem.evaluate xs db target = (.val ws, targetNext) ∧
      List.Forall₂ ValueRel vs ws.reverse ∧ xs.length = vs.length ∧
      op ≠ .src .opapp ∧ op ≠ .src (.thunkOp .forceThunk) →
    ∃ targetResult targetLast,
      ClosSem.evaluate [compileOp trace op xs] db target = (targetResult, targetLast) ∧
      StateRel sourceNext targetLast ∧
      SemanticPrimitivesProps.resultRel (List.Forall₂ ValueRel) ValueRel
        (Flapjack.EvaluateHOL.listResult result) targetResult := by
  intro opEq premises
  subst op
  simp [FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory,
    FlatSem.doAppData, FlatSem.doAppCopy] at premises

end Flapjack.Compiler.Backend.FlatToClos

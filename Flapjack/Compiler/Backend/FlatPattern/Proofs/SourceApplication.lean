module

public import Flapjack.Compiler.Backend.FlatPattern.Proofs.FunctionApplication
public import Flapjack.Compiler.Backend.FlatPattern.Proofs.PatternRelation
public import Flapjack.Compiler.Backend.FlatProps.SimpleDoApp

@[expose] public section

/-! Source-primitive applications in the flat pattern simulation. -/
namespace Flapjack.Compiler.Backend.FlatPattern
open Flapjack Flapjack.AstHOL Flapjack.Compiler.Backend
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Flapjack evaluation infrastructure for nonrecursive applications: the
evaluated arguments are dispatched to the primitive evaluator. -/
theorem evaluate_simpleApp_values {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (state next : FlatSem.State C F) (trace : BackendCommon.Tra) (op : FlatLang.Op)
    (args : List FlatLang.Exp) (values : List FlatSem.Value)
    (notCall : op ≠ .src .opapp) (notEval : op ≠ .src .eval)
    (notForce : op ≠ .src (.thunkOp .forceThunk))
    (argsRun : FlatSem.evaluate env state args.reverse = (next, .val values)) :
    FlatSem.evaluate env state [.app trace op args] =
      FlatSem.applyResult { next with clock := min state.clock next.clock } op values.reverse := by
  cases op with
  | src sourceOp => cases sourceOp <;> simp_all [FlatSem.evaluate, FlatSem.fixClock]
  | globalVarAlloc _ | globalVarInit _ | globalVarLookup _ | tagLenEq _ _ | lenEq _ | el _ | id =>
    simp [FlatSem.evaluate, FlatSem.fixClock, argsRun]

@[hol "cakeml/compiler/backend/proofs/flat_patternProofScript.sml" "do_app_thm"]
theorem doApp_simulation {C F : Type} (op : FlatLang.Op) (cfg : Config)
    (source : FlatSem.State C F) (values : List FlatSem.Value)
    (sourceFinal : FlatSem.State C F) (result : Result FlatSem.Value FlatSem.Value)
    (target : FlatSem.State C F) (values' : List FlatSem.Value)
    (run : FlatSem.doApp source op values = some (sourceFinal, result))
    (premises : StateRel cfg source target ∧ List.Forall₂ ValueRel values values') :
    ∃ targetFinal result', SemanticPrimitivesProps.resultRel ValueRel ValueRel result result' ∧
      StateRel cfg sourceFinal targetFinal ∧ FlatSem.doApp target op values' = some (targetFinal, result') := by
  exact FlatProps.simpleDoApp ValueRel (StateRel cfg) op
    ⟨simpleValueRel_valueRel, simpleStateRel_stateRel cfg⟩
    source values sourceFinal result target values' run premises

end Flapjack.Compiler.Backend.FlatPattern

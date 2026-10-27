import Flapjack.Compiler.Backend.SourceToFlat.Proofs.EvaluateControl
import Flapjack.Compiler.Backend.SourceToFlat.Proofs.MemoryOps

/-! Expression-level primitive application simulations. These use the
preliminary factored relations and are not yet reviewed HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.SourceToFlat
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL

/-- Allocating a reference after evaluating its operand preserves the value
and state relations, including operand errors and the flat store offset. -/
theorem exprSim_opref {C F : Type} (genv : GlobalEnv) (compMap : Environment) (trace : List VarN)
    (sourceEnv : SemEnv SemanticPrimitivesHOL.Value) (flatEnv : FlatSem.Environment FlatSem.Value)
    (sourceState : SemanticPrimitivesHOL.State F) (flatState : FlatSem.State C F) (body : AstHOL.Exp)
    (bodySim : ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState body) :
    ExprSim genv compMap trace sourceEnv flatEnv sourceState flatState (.app .opref [body]) := by
  unfold ExprSim at bodySim
  cases sourceRun : EvaluateHOL.evaluate sourceState sourceEnv [body] with
  | mk sourceNext sourceResult =>
    rw [sourceRun] at bodySim
    cases flatRun : FlatSem.evaluate flatEnv flatState [compileExp trace compMap body] with
    | mk flatNext flatResult =>
      rw [flatRun] at bodySim
      obtain ⟨related, nextRel⟩ := bodySim
      cases sourceResult with
      | err error =>
        cases error with
        | raise value =>
          cases related with
          | raise valueRel =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.raise valueRel, nextRel⟩
        | abort error =>
          cases related with
          | abort =>
            unfold ExprSim
            rw [EvaluateHOL.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
            simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
            rw [FlatSem.evaluate]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
            rw [(FlatSem.fixClock_evaluations flatEnv flatState
              [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
            exact ⟨.abort error, nextRel⟩
      | val values =>
        obtain ⟨value, rfl⟩ := EvaluateProps.evaluateSingFull sourceState sourceNext sourceEnv body values sourceRun
        cases related with
        | value valuesRel =>
          cases valuesRel with
          | cons valueRel tail =>
            cases tail with
            | nil =>
              rename_i flatValue
              obtain ⟨sourceApp, flatApp, locationRel, stateRel, _⟩ :=
                opref_related genv sourceNext flatNext nextRel value flatValue valueRel
              unfold ExprSim
              rw [EvaluateHOL.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
              rw [(EvaluateHOL.fixClockEvaluate sourceState sourceEnv [body] []).1, sourceRun]
              simp only [compileExp, compileExps, reduceCtorEq, ↓reduceIte]
              rw [FlatSem.evaluate]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append]
              rw [(FlatSem.fixClock_evaluations flatEnv flatState
                [compileExp trace compMap body] (FlatLang.Exp.lit .none (.intLit 0)) []).1, flatRun]
              simp only [List.reverse_cons, List.reverse_nil, List.nil_append, getOpClass, astOpToFlatOp]
              simp [doApp, doAppNumericCore, sourceApp, FlatSem.applyResult, FlatSem.doApp,
                FlatSem.doAppNumeric, flatApp, EvaluateHOL.listResult]
              exact ⟨.value (.cons locationRel .nil), stateRel⟩

end Flapjack.Compiler.Backend.SourceToFlat

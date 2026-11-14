module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationApp
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationBase
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationCons
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationConstructors
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDeclarations
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDecsCons
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDenv
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDlet
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationExpressions
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationHandle
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationIf
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationLet
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationLetrec
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationLog
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationMat
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationMatchCons
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationModules
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationStamps
public import Flapjack.EvaluateHOL.Induction

@[expose] public section

/-! Mutual induction and complete source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL


/-- The full source evaluator simulation, including the independent inhabited
unused HOL expression binder. The evaluator inherits the rational-cut real
number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem eval_simulation {Config F : Type} (ci : CompilerInstance Config) :
    (∀ (s : State F) (env : SemEnv Value) (exps : List AstHOL.Exp)
      (s' : State F) (res : Result (List Value) Value) (t : State F) (env' : SemEnv Value),
      evaluate s env exps = (s', res) ∧ stateRel ci s t ∧
        envRel (ValueRel (oracleState t.evalState)) env env' ∧ res ≠ .err (.abort .typeError) →
      ∃ es' t' res', evaluate t env' exps = (t', res') ∧ stateRel ci s' t' ∧
        es' = oracleState t'.evalState ∧ resultRel (List.Forall₂ (ValueRel es')) (ValueRel es') res res' ∧
        envStoreForward (oracleState t.evalState) es' ∧
        (¬ abort res' → envStackForward (oracleState t.evalState) es')) ∧
    (∀ (s : State F) (env : SemEnv Value) (x : Value) (rows : List (Pat × AstHOL.Exp)) (errX : Value)
      (s' : State F) (res : Result (List Value) Value) (es : EvalOracleState) (t : State F)
      (env' : SemEnv Value) (y errY : Value),
      evaluateMatch s env x rows errX = (s', res) ∧ stateRel ci s t ∧ es = oracleState t.evalState ∧
        envRel (ValueRel es) env env' ∧ ValueRel es x y ∧ ValueRel es errX errY ∧
        res ≠ .err (.abort .typeError) →
      ∃ es' t' res', evaluateMatch t env' y rows errY = (t', res') ∧ stateRel ci s' t' ∧
        es' = oracleState t'.evalState ∧ resultRel (List.Forall₂ (ValueRel es')) (ValueRel es') res res' ∧
        envStoreForward es es' ∧ (¬ abort res' → envStackForward es es')) ∧
    (∀ (s : State F) (env : SemEnv Value) (decs : List Dec) (s' : State F)
      (res : Result (SemEnv Value) Value) (t : State F) (env' : SemEnv Value),
      evaluateDecs s env decs = (s', res) ∧ stateRel ci s t ∧
        envRel (ValueRel (oracleState t.evalState)) env env' ∧ res ≠ .err (.abort .typeError) →
      ∃ es' t' res', evaluateDecs t env' decs = (t', res') ∧ stateRel ci s' t' ∧
        es' = oracleState t'.evalState ∧ resultRel (envRel (ValueRel es')) (ValueRel es') res res' ∧
        envStoreForward (oracleState t.evalState) es' ∧
        (¬ abort res' → envStackForward (oracleState t.evalState) es')) := by
  apply fullEvaluateInd (ExpsSimAt ci) (MatchSimAt ci) (DecsSimAt ci)
  exact ⟨evalSimulation_ExpsNil ci, evalSimulation_ExpsCons ci, evalSimulation_Lit ci,
    evalSimulation_Raise ci, evalSimulation_Handle ci, evalSimulation_Con ci,
    evalSimulation_Var ci, evalSimulation_Fn ci, evalSimulation_App ci,
    evalSimulation_Log ci, evalSimulation_If ci, evalSimulation_Mat ci,
    evalSimulation_Let ci, evalSimulation_Letrec ci, evalSimulation_Tannot ci,
    evalSimulation_Lannot ci, evalSimulation_MatchNil ci, evalSimulation_MatchCons ci,
    evalSimulation_DecsNil ci, evalSimulation_DecsCons ci, evalSimulation_Dlet ci,
    evalSimulation_Dletrec ci, evalSimulation_Dtype ci, evalSimulation_Dtabbrev ci,
    evalSimulation_Denv ci, evalSimulation_Dexn ci, evalSimulation_Dmod ci,
    evalSimulation_Dlocal ci⟩

end Flapjack.Compiler.Backend.SourceEval.Proofs

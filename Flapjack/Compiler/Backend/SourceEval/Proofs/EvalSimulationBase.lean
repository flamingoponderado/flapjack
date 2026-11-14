module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.StateRelation
public import Flapjack.Compiler.Backend.SourceEval.Proofs.Abort
public import Flapjack.EvaluateHOL.Definition
public import Flapjack.SemanticPrimitivesProps.ResultRelation
public import Flapjack.NamespaceProps.EmptyLookup

@[expose] public section

/-! Empty-list cases of source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.NamespaceHOL Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Empty expression-list case; HOL's unused `es` has an independent inhabited type. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_ExpsNil {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value)
    (s' : State F) (res : Result (List Value) Value) (t : State F) (env' : SemEnv Value)
    (premises : evaluate s env [] = (s', res) ∧ stateRel ci s t ∧
      envRel (ValueRel (oracleState t.evalState)) env env' ∧ res ≠ .err (.abort .typeError)) :
    ∃ es' t' res', evaluate t env' [] = (t', res') ∧ stateRel ci s' t' ∧
      es' = oracleState t'.evalState ∧ resultRel (List.Forall₂ (ValueRel es')) (ValueRel es') res res' ∧
      envStoreForward (oracleState t.evalState) es' ∧
      (¬ abort res' → envStackForward (oracleState t.evalState) es') := by
  obtain ⟨run, related, _, _⟩ := premises
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨oracleState t.evalState, t, .val [], ?_, related, rfl, ?_,
    envStoreForward_refl _, fun _ => envStackForward_refl _⟩
  · simp [evaluate]
  · simp [resultRel]

/-- Empty match-row case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_MatchNil {Config F : Type} (ci : CompilerInstance Config) (s : State F) (env : SemEnv Value)
    (x : Value) (err_x : Value) (s' : State F) (res : Result (List Value) Value)
    (es : EvalOracleState) (t : State F) (env' : SemEnv Value) (y err_y : Value)
    (premises : evaluateMatch s env x [] err_x = (s', res) ∧ stateRel ci s t ∧
      es = oracleState t.evalState ∧ envRel (ValueRel es) env env' ∧ ValueRel es x y ∧
      ValueRel es err_x err_y ∧ res ≠ .err (.abort .typeError)) :
    ∃ es' t' res', evaluateMatch t env' y [] err_y = (t', res') ∧ stateRel ci s' t' ∧
      es' = oracleState t'.evalState ∧ resultRel (List.Forall₂ (ValueRel es')) (ValueRel es') res res' ∧
      envStoreForward es es' ∧ (¬ abort res' → envStackForward es es') := by
  obtain ⟨run, related, rfl, _, _, errRelated, _⟩ := premises
  simp [evaluateMatch] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨oracleState t.evalState, t, .err (.raise err_y), ?_, related, rfl, ?_,
    envStoreForward_refl _, fun _ => envStackForward_refl _⟩
  · simp [evaluateMatch]
  · exact errRelated

/-- Empty declaration-list case of the original evaluator induction. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_DecsNil {Config F : Type} (ci : CompilerInstance Config) (s : State F) (env : SemEnv Value)
    (s' : State F) (res : Result (SemEnv Value) Value) (t : State F) (env' : SemEnv Value)
    (premises : evaluateDecs s env [] = (s', res) ∧ stateRel ci s t ∧
      envRel (ValueRel (oracleState t.evalState)) env env' ∧ res ≠ .err (.abort .typeError)) :
    ∃ es' t' res', evaluateDecs t env' [] = (t', res') ∧ stateRel ci s' t' ∧
      es' = oracleState t'.evalState ∧ resultRel (envRel (ValueRel es')) (ValueRel es') res res' ∧
      envStoreForward (oracleState t.evalState) es' ∧
      (¬ abort res' → envStackForward (oracleState t.evalState) es') := by
  obtain ⟨run, related, _, _⟩ := premises
  simp [evaluateDecs] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨oracleState t.evalState, t, .val ({ v := nsEmpty, c := nsEmpty } : SemEnv Value), ?_, related, rfl, ?_,
    envStoreForward_refl _, fun _ => envStackForward_refl _⟩
  · simp only [evaluateDecs]
    rfl
  · change envRel (ValueRel (oracleState t.evalState))
      ({ v := nsEmpty, c := nsEmpty } : SemEnv Value) { v := nsEmpty, c := nsEmpty }
    simp [envRel, nsLookup_nsEmpty]

end Flapjack.Compiler.Backend.SourceEval.Proofs

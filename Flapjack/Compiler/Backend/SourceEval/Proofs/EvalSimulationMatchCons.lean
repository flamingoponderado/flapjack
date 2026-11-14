module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationHandle
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentBind
public import Flapjack.NamespaceProps

@[expose] public section

/-! Pattern-match row case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- A pattern-match row preserves the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_MatchCons {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (x : Value) (pat : Pat) (expr : Flapjack.AstHOL.Exp)
    (rows : List (Pat × Flapjack.AstHOL.Exp)) (err : Value)
    (ih : (∀ bindings, (patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .match bindings →
      ExpsSimAt ci s { env with v := nsAppend (alistToNs bindings) env.v } [expr]) ∧
      ((patBindings pat).Nodup ∧ pmatch env.c s.refs pat x [] = .noMatch →
        MatchSimAt ci s env x rows err)) :
    MatchSimAt ci s env x ((pat, expr) :: rows) err := by
  obtain ⟨bodyIH, restIH⟩ := ih
  intro s' res es t env' y err' ⟨run, related, esEq, envRelated, xRelated, errRelated, safe⟩
  subst es
  by_cases distinct : (patBindings pat).Nodup
  · have matchRelated := pmatchDrule env s pat x (pmatch env.c s.refs pat x []) ci t env' y
      ⟨rfl, related, envRelated, xRelated⟩
    cases sourceMatch : pmatch env.c s.refs pat x [] with
    | typeError =>
      simp [evaluateMatch, distinct, sourceMatch, typeError] at run
      obtain ⟨_, rfl⟩ := run
      exact (safe rfl).elim
    | noMatch =>
      have targetMatch : pmatch env'.c t.refs pat y [] = .noMatch := by
        simpa [sourceMatch, matchResultRel] using matchRelated
      have sourceRun : evaluateMatch s env x rows err = (s', res) := by
        simpa [evaluateMatch, distinct, sourceMatch] using run
      obtain ⟨es', t', res', targetRun, rel', eq, resultRel', fwd, stack⟩ :=
        restIH ⟨distinct, sourceMatch⟩ s' res (oracleState t.evalState) t env' y err'
          ⟨sourceRun, related, rfl, envRelated, xRelated, errRelated, safe⟩
      exact ⟨es', t', res', by simpa [evaluateMatch, distinct, targetMatch] using targetRun,
        rel', eq, resultRel', fwd, stack⟩
    | «match» bindings =>
      obtain ⟨bindings', targetMatch, bindingsRel⟩ := by
        simpa [sourceMatch, matchResultRel] using matchRelated
      have sourceRun : evaluate s { env with v := nsAppend (alistToNs bindings) env.v } [expr] = (s', res) := by
        simpa [evaluateMatch, distinct, sourceMatch] using run
      have nextEnvRelated : envRel (ValueRel (oracleState t.evalState))
          { env with v := nsAppend (alistToNs bindings) env.v }
          { env' with v := nsAppend (alistToNs bindings') env'.v } := by
        rw [nsAppend_to_nsBindList, nsAppend_to_nsBindList]
        exact envRel_add_nsBindList _ env env.v env' env'.v bindings bindings' ⟨envRelated, bindingsRel⟩
      obtain ⟨es', t', res', targetRun, rel', eq, resultRel', fwd, stack⟩ :=
        bodyIH bindings ⟨distinct, sourceMatch⟩ s' res t
          { env' with v := nsAppend (alistToNs bindings') env'.v }
          ⟨sourceRun, related, nextEnvRelated, safe⟩
      exact ⟨es', t', res', by simpa [evaluateMatch, distinct, targetMatch] using targetRun,
        rel', eq, resultRel', fwd, stack⟩
  · simp [evaluateMatch, distinct, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
end Flapjack.Compiler.Backend.SourceEval.Proofs

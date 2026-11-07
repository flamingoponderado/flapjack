import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationCons
import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentBind
import Flapjack.SemanticPrimitivesProps.RecursiveFunctions

/-! Recursive-binding case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Recursive bindings preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Letrec {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (funs : List (VarN × VarN × Flapjack.AstHOL.Exp))
    (body : Flapjack.AstHOL.Exp)
    (ih : (funs.map fun (name, _, _) => name).Nodup →
      ExpsSimAt (A := A) ci s { env with v := buildRecEnv funs env env.v } [body]) :
    ExpsSimAt (A := A) ci s env [.letrec funs body] := by
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  by_cases distinct : (funs.map fun (name, _, _) => name).Nodup
  · have sourceRun : evaluate s { env with v := buildRecEnv funs env env.v } [body] = (s', res) := by
      simpa [evaluate, distinct] using run
    have bindingsRel : ∀ xs : List (VarN × VarN × Flapjack.AstHOL.Exp),
        List.Forall₂ (Flapjack.holRprod (· = ·) (ValueRel (oracleState t.evalState)))
          (xs.map fun (f, _, _) => (f, Value.recclosure env funs f))
          (xs.map fun (f, _, _) => (f, Value.recclosure env' funs f)) := by
      intro xs
      induction xs with
      | nil => exact .nil
      | cons item rest ih =>
        obtain ⟨name, arg, exp⟩ := item
        exact .cons ⟨rfl, .recclosure ((valueEnvRel_iff _ _ _).mpr envRelated)⟩ ih
    have extended : envRel (ValueRel (oracleState t.evalState))
        { env with v := buildRecEnv funs env env.v }
        { env' with v := buildRecEnv funs env' env'.v } := by
      rw [buildRecEnv_merge funs () env env.v, buildRecEnv_merge funs () env' env'.v]
      rw [nsAppend_to_nsBindList, nsAppend_to_nsBindList]
      exact envRel_add_nsBindList _ env env.v env' env'.v _ _ ⟨envRelated, bindingsRel funs⟩
    obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
      ih distinct s' res es t { env' with v := buildRecEnv funs env' env'.v }
        ⟨sourceRun, related, extended, safe⟩
    exact ⟨es₁, t₁, r₁, by simpa [evaluate, distinct] using targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩
  · simp [evaluate, distinct, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
end Flapjack.Compiler.Backend.SourceEval.Proofs

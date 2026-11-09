module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDeclarations
public import Flapjack.Compiler.Backend.SourceEval.Proofs.DeclareEnvSimulation

@[expose] public section

/-! Environment-declaration case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Environment declarations preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Denv {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (name : VarN) : DecsSimAt ci s env [.denv name] := by
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  cases declared : declareEnv s.evalState env with
  | none =>
    simp [evaluateDecs, declared, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
  | some pair =>
    obtain ⟨value, es⟩ := pair
    simp [evaluateDecs, declared] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨value', es₂, fwd, targetDeclared, valueRel, stateRel', stack⟩ :=
      declareEnv_sim s env value es ci t env' ⟨declared, related, envRelated⟩
    refine ⟨oracleState es₂, { t with evalState := es₂ },
      .val { v := nsSing name value', c := nsEmpty }, ?_, stateRel', rfl, ?_, fwd, ?_⟩
    · simp [evaluateDecs, targetDeclared]
    · change envRel (ValueRel (oracleState es₂))
        ({ v := nsBind name value nsEmpty, c := nsEmpty } : SemEnv Value)
        ({ v := nsBind name value' nsEmpty, c := nsEmpty } : SemEnv Value)
      apply envRel_add_nsBind _ ({ v := nsEmpty, c := nsEmpty } : SemEnv Value) nsEmpty
        ({ v := nsEmpty, c := nsEmpty } : SemEnv Value) nsEmpty value value' name
      refine ⟨?_, valueRel⟩
      simp [envRel, nsLookup_nsEmpty]
    · intro _
      exact stack
end Flapjack.Compiler.Backend.SourceEval.Proofs

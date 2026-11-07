import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationCons
import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentRecursive
import Flapjack.NamespaceProps.EmptyLookup

/-! Declaration cases of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Recursive function declarations preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Dletrec {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs)
    (funs : List (VarN × VarN × Flapjack.AstHOL.Exp)) :
    DecsSimAt ci s env [.dletrec loc funs] := by
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  have constructors : env.c = env'.c := envRelated.1
  by_cases check : (decide (funs.map fun (name, _, _) => name).Nodup &&
      funs.all (fun (_, _, expr) => everyExp (oneConCheck env.c) expr)) = true
  · have targetCheck : (decide (funs.map fun (name, _, _) => name).Nodup &&
      funs.all (fun (_, _, expr) => everyExp (oneConCheck env'.c) expr)) = true := by
        simpa [constructors] using check
    simp [evaluateDecs, check] at run
    obtain ⟨rfl, rfl⟩ := run
    refine ⟨oracleState t.evalState, t, .val { v := buildRecEnv funs env' nsEmpty, c := nsEmpty },
      ?_, related, rfl, ?_, envStoreForward_refl _, fun _ => envStackForward_refl _⟩
    · simp [evaluateDecs, targetCheck]
    · change envRel (ValueRel (oracleState t.evalState))
        { v := buildRecEnv funs env nsEmpty, c := nsEmpty }
        { v := buildRecEnv funs env' nsEmpty, c := nsEmpty }
      apply envRel_buildRecEnv _ { v := nsEmpty, c := nsEmpty } { v := nsEmpty, c := nsEmpty }
        env env' nsEmpty nsEmpty funs
      refine ⟨?_, envRelated⟩
      simp [envRel, nsLookup_nsEmpty]
  · simp [evaluateDecs, check, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim

/-- Type abbreviations preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Dtabbrev {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (loc : Flapjack.Misc.Location.Locs) (vars : List TvarN) (name : TypeN) (typ : AstT) :
    DecsSimAt ci s env [.dtabbrev loc vars name typ] := by
  intro s' res t env' ⟨run, related, envRelated, safe⟩
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

module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleExtractAgrees
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulation
public import Flapjack.Compiler.Backend.SourceEval.Proofs.SimulationPrerequisites
public import Flapjack.SemanticsHOL

@[expose] public section

/-! Initial compiler state of the first extracted oracle event. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL
open Flapjack.EvaluateHOL Flapjack.NamespaceHOL Flapjack.SemanticsHOL

/-- The first extracted event starts from the initial compiler state when the
source program cannot fail. The evaluator inherits the rational-cut real-number
assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "extract_oracle_0_st"]
theorem extract_oracle_0_st {Config F : Type} (t : State F) (env : SemEnv Value)
    (decs : List Dec) (r : CompilerArgs) (s : State F) (ci : CompilerInstance Config)
    (premises : extractOracle t env decs 0 = some r ∧ ¬ semanticsProg s env decs .fail ∧
      stateRel ci s t ∧ nsAll (fun _ value => concreteValue value = true) env.v) :
    r.2.1 = ci.configV ci.initState := by
  classical
  obtain ⟨extracted, noFail, related, concrete⟩ := premises
  by_cases existsClock : ∃ n next result,
      evaluateDecs { t with clock := n } env decs = (next, result) ∧
        0 < ((oracleState next.evalState).oracle 0).1.1
  · obtain ⟨target, targetResult, targetRun, targetBound⟩ := Nat.find_spec existsClock
    cases sourceRun : evaluateDecs { s with clock := Nat.find existsClock } env decs with
    | mk source result =>
      have safe : result ≠ .err (.abort .typeError) := by
        intro bad
        apply noFail
        change ∃ clock, (evaluateProgWithClock s env clock decs).2 = .err (.abort .typeError)
        refine ⟨Nat.find existsClock, ?_⟩
        unfold evaluateProgWithClock
        rw [sourceRun]
        exact bad
      have relation := stateRel_setClock ci s t (Nat.find existsClock) related
      obtain ⟨es, target', result', targetRun', related', esEq, _, _, _⟩ :=
        (eval_simulation ci).2.2 _ env decs source result _ env
          ⟨sourceRun, relation, envRel_concrete env _ concrete, safe⟩
      rw [targetRun] at targetRun'
      cases targetRun'
      obtain ⟨decState, oracle, refs, targetEq, stores, sourceEq, callback, configEq, decoder, compiler,
        zero, positive, counters, length, wf⟩ := related'
      have positiveCount : 0 < (oracle.oracle 0).1.1 := by
        simpa [targetEq, oracleState] using targetBound
      have initial := positive positiveCount
      simp only [extractOracle, Flapjack.holOLeast, dif_pos existsClock, targetRun] at extracted
      cases extracted
      simpa [targetEq, oracleState] using initial
  · simp only [extractOracle, Flapjack.holOLeast, dif_neg existsClock] at extracted
    contradiction
end Flapjack.Compiler.Backend.SourceEval.Proofs

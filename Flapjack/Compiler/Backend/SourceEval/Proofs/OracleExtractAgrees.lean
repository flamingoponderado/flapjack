import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleCommonPrefix
import Flapjack.Compiler.Backend.SourceEval.Proofs.StateRelation

/-! Agreement of an extracted oracle with a recorded declaration evaluation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.EvaluateHOL

/-- An oracle agreeing with defined extracted compiler events agrees with the
recorded evaluation state. The evaluator inherits the rational-cut real-number
assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "extract_oracle_agrees"]
theorem extract_oracle_agrees {Config F : Type} (t : State F) (k : Nat) (env : SemEnv Value)
    (decs : List Dec) (t' : State F) (res : Result (SemEnv Value) Value)
    (ci : CompilerInstance Config) (s : State F) (oracle : EvalOracleFun)
    (premises : evaluateDecs { t with clock := k } env decs = (t', res) ∧ stateRel ci s t ∧
      (∀ i r, extractOracle t env decs i = some r ∧ mkCompilerFunFromCi ci r ≠ none → oracle i = r)) :
    oracleAgrees oracle t'.evalState := by
  classical
  obtain ⟨run, relation, agrees⟩ := premises
  obtain ⟨decState, initial, refs, target, stores, sourceEval, callback, stateEq, decoder, compiler,
    initialZero, initialPositive, counters, length, initialWf⟩ := relation
  have recording : isRecord ci t.evalState := by
    rw [target]
    exact callback
  have initialWf' : recordedOracleWellFormed (mkCompilerFunFromCi ci) (oracleState t.evalState).oracle := by
    rw [target]
    exact initialWf
  have recorded := (evaluate_is_record_forward ci).2.2 { t with clock := k } env decs t' res ⟨run, recording⟩
  have finalWf := recorded.2.2 initialWf'
  obtain ⟨final, finalEq⟩ := isRecord_imp ci t'.evalState recorded.1
  rw [finalEq] at finalWf ⊢
  change ∀ j, j < (final.oracle 0).1.1 → oracle j = final.oracle (j + 1)
  intro j bound
  have existsClock : ∃ n next result,
      evaluateDecs { t with clock := n } env decs = (next, result) ∧
        j < ((oracleState next.evalState).oracle 0).1.1 := ⟨k, t', res, run, by simpa [finalEq, oracleState] using bound⟩
  let least := Nat.find existsClock
  obtain ⟨next, result, nextRun, nextBound⟩ := Nat.find_spec existsClock
  have sameEvent := evaluate_decs_clock_record_common_prefix { t with clock := k } env decs t' res least next result ci j
    ⟨run, by simpa [least] using nextRun, recording, by simpa [finalEq, oracleState] using bound, nextBound⟩
  have defined : mkCompilerFunFromCi ci (final.oracle (j + 1)) ≠ none := by
    apply recordedOracleWellFormed_defined (mkCompilerFunFromCi ci) final.oracle (j + 1)
    exact ⟨by simpa [oracleState] using finalWf, by omega, by omega⟩
  have extracted : extractOracle t env decs j = some ((oracleState next.evalState).oracle (j + 1)) := by
    simp only [extractOracle, Flapjack.holOLeast, dif_pos existsClock]
    rw [nextRun]
  have sameEvent' : final.oracle (j + 1) = (oracleState next.evalState).oracle (j + 1) := by
    simpa [finalEq, oracleState] using sameEvent
  apply (agrees j _ ⟨extracted, ?_⟩).trans sameEvent'.symm
  simpa [← sameEvent'] using defined
end Flapjack.Compiler.Backend.SourceEval.Proofs

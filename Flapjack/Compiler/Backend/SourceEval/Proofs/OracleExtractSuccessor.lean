module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleExtractInitial

@[expose] public section

/-! Consecutive extracted compiler events. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL
open Flapjack.EvaluateHOL Flapjack.NamespaceHOL Flapjack.SemanticsHOL

/-- Consecutive extracted events are linked by the compiler transition. The
evaluator inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "extract_oracle_SUC_st"]
theorem extract_oracle_SUC_st {Config F : Type} (t : State F) (env : SemEnv Value)
    (decs : List Dec) (i : Nat) (ci : CompilerInstance Config) (s : State F)
    (premises : (extractOracle t env decs (i + 1)).isSome ∧ stateRel ci s t ∧
      nsAll (fun _ value => concreteValue value = true) env.v ∧ ¬ semanticsProg s env decs .fail) :
    ∃ r r' x, extractOracle t env decs (i + 1) = some r' ∧ extractOracle t env decs i = some r ∧
      mkCompilerFunFromCi ci r = some x ∧ r'.2.1 = x.1 := by
  classical
  obtain ⟨success, related, concrete, noFail⟩ := premises
  have previous := extractOracle_isSome_succ t env decs i success
  cases earlier : extractOracle t env decs i with
  | none => simp [earlier] at previous
  | some r =>
    cases later : extractOracle t env decs (i + 1) with
    | none => simp [later] at success
    | some r' =>
      by_cases existsClock : ∃ n next result,
          evaluateDecs { t with clock := n } env decs = (next, result) ∧
            i + 1 < ((oracleState next.evalState).oracle 0).1.1
      · obtain ⟨target, targetResult, targetRun, targetBound⟩ := Nat.find_spec existsClock
        let oracle : EvalOracleFun := fun j => (extractOracle t env decs j).getD ((0, 0), .conv none [], [])
        have agreesInput : ∀ j event, extractOracle t env decs j = some event ∧
            mkCompilerFunFromCi ci event ≠ none → oracle j = event := by
          intro j event ⟨found, _⟩
          simp [oracle, found]
        have agrees := extract_oracle_agrees t (Nat.find existsClock) env decs target targetResult ci s oracle
          ⟨targetRun, related, agreesInput⟩
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
            (eval_simulation (A := Unit) ci).2.2 _ env decs source result _ env
              ⟨sourceRun, relation, envRel_concrete env _ concrete, safe⟩
          rw [targetRun] at targetRun'
          cases targetRun'
          have earlierEq := oracleAgrees_stateRel oracle target ci source i agrees related' (by omega)
          have laterEq := oracleAgrees_stateRel oracle target ci source (i + 1) agrees related' targetBound
          obtain ⟨decState, recorded, refs, targetEq, stores, sourceEq, callback, configEq, decoder, compiler,
            zero, positive, counters, length, wf⟩ := related'
          have eventBound : i + 1 < (recorded.oracle 0).1.1 := by simpa [targetEq, oracleState] using targetBound
          obtain ⟨result, compiled, next⟩ := wf.2 (i + 1) ⟨eventBound, by omega⟩
          have earlierEvent : r = recorded.oracle (i + 1) := by
            simpa [oracle, earlier, targetEq, oracleState] using earlierEq
          have laterEvent : r' = recorded.oracle (i + 1 + 1) := by
            simpa [oracle, later, targetEq, oracleState] using laterEq
          refine ⟨r, r', result, rfl, rfl, ?_, ?_⟩
          · simpa [earlierEvent] using compiled
          · simpa [laterEvent] using next
      · simp only [extractOracle, Flapjack.holOLeast, dite_eq_right existsClock] at later
        contradiction
end Flapjack.Compiler.Backend.SourceEval.Proofs

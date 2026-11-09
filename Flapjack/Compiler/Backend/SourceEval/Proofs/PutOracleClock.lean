module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.GetOracleProps
public import Flapjack.Compiler.Backend.SourceEval.Proofs.InsertCorrect
public import Flapjack.EvaluateProps.NoEval

@[expose] public section

/-! Clocked program evaluation with the extracted compiler oracle installed. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL
open Flapjack.EvaluateHOL Flapjack.NamespaceHOL Flapjack.SemanticsHOL

/-- Installing an agreeing compiler oracle preserves clocked program FFI and
result shape. The evaluator inherits the rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "evaluate_prog_with_clock_put_oracle"]
theorem evaluate_prog_with_clock_put_oracle {Config F : Type} (oracle : EvalOracleFun)
    (ci : CompilerInstance Config) (s : State F) (env : SemEnv Value) (decs : List Dec)
    (k : Nat) (ffi : HolFfiState F) (res : Result (SemEnv Value) Value)
    (premises : precondEvalState oracle ci s env decs ∧ evaluateProgWithClock s env k decs = (ffi, res) ∧
      res ≠ .err (.abort .typeError) ∧ s.refs = [] ∧
      nsAll (fun _ value => concreteValue value = true) env.v ∧ ¬ semanticsProg s env decs .fail) :
    ∃ res', evaluateProgWithClock { s with evalState := putOracle ci oracle } env k decs = (ffi, res') ∧
      resultRel (fun _ _ => True) (fun _ _ => True) res res' := by
  obtain ⟨precond, programRun, safe, emptyRefs, concrete, noFail⟩ := premises
  cases sourceRun : evaluateDecs { s with clock := k } env decs with
  | mk after result =>
    have sourceEq : (after.ffi, result) = (ffi, res) := by
      simpa [evaluateProgWithClock, sourceRun] using programRun
    obtain ⟨ffiEq, rfl⟩ := Prod.mk.inj sourceEq
    cases stateEq : s.evalState with
    | none =>
      have sim := (Flapjack.EvaluateProps.eval_no_eval_simulation (putOracle ci oracle)).2.2
        { s with clock := k } env decs after result ⟨sourceRun, by simpa using stateEq, safe⟩
      refine ⟨result, ?_, ?_⟩
      · simp [evaluateProgWithClock, sim.2, ffiEq]
      · cases result with
        | val _ => trivial
        | err error => cases error <;> simp [resultRel, excRel]
    | some st =>
      cases st with
      | evalOracle st =>
        simp [precondEvalState, stateEq] at precond
      | evalDecs st =>
        simp only [precondEvalState, stateEq] at precond
        obtain ⟨initEq, extended, agreesEvents⟩ := precond
        have stInit : st = ⟨mkCompilerFunFromCi ci, ci.configV ci.initState, (0, 0, 1),
            vFunAbs ci.decsDom ci.decsV⟩ := by
          exact EvalState.evalDecs.inj (by simpa [mkInitEvalState] using initEq)
        subst st
        let initial : EvalOracleState := ⟨fun _ => ((0, 0), ci.configV ci.initState, []),
          doEvalRecord ci, [[]], 0⟩
        let t : State F := { s with evalState := some (.evalOracle initial) }
        have relation : stateRel ci s t := by
          refine ⟨⟨mkCompilerFunFromCi ci, ci.configV ci.initState, (0, 0, 1), vFunAbs ci.decsDom ci.decsV⟩,
            initial, [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals simp [t, initial, emptyRefs, stateEq, recordedOracleWellFormed,
            Flapjack.holEl, Flapjack.holHd]
        have relatedClock := stateRel_setClock ci s t k relation
        obtain ⟨finalOracle, target, targetRes, targetRun, targetRel, finalEq, resultRelated, _, _⟩ :=
          (eval_simulation (A := Unit) ci).2.2 _ env decs after result _ env
            ⟨sourceRun, relatedClock, envRel_concrete env _ concrete, safe⟩
        have finalSafe : targetRes ≠ .err (.abort .typeError) := by
          intro bad
          subst targetRes
          cases result with
          | val _ => cases resultRelated
          | err error =>
            cases error with
            | raise _ => cases resultRelated
            | abort reason =>
              have equal : reason = .typeError := by simpa [resultRel, excRel] using resultRelated
              subst reason
              exact safe rfl
        have initialRecorded : isRecord ci t.evalState := by simp [t, initial, isRecord]
        have extractedAgrees : ∀ i r, extractOracle t env decs i = some r ∧
            mkCompilerFunFromCi ci r ≠ none → oracle i = r := by
          intro i r ⟨found, defined⟩
          cases compiled : mkCompilerFunFromCi ci r with
          | none => exact (defined compiled).elim
          | some x =>
            apply agreesEvents i r x
            exact ⟨by simpa [getOracle, t, initial] using found, compiled⟩
        have finalAgrees := extract_oracle_agrees t k env decs target targetRes ci s oracle
          ⟨targetRun, relation, extractedAgrees⟩
        have inserted := (insert_oracle_correct ci oracle).2.2 { t with clock := k } env decs target targetRes
          ⟨targetRun, by simpa using initialRecorded, finalAgrees, extended, finalSafe⟩
        have targetFfi : target.ffi = ffi := by
          obtain ⟨_, _, _, eq, _, _, _⟩ := targetRel
          have eqFfi := congrArg (fun st : State F => st.ffi) eq
          simpa [ffiEq] using eqFfi
        have topRel : resultRel (fun _ _ => True) (fun _ _ => True) result targetRes := by
          cases result with
          | val value =>
            cases targetRes with
            | val other => trivial
            | err error => cases resultRelated
          | err error =>
            cases targetRes with
            | val other => cases resultRelated
            | err other =>
              cases error <;> cases other <;> simp_all only [resultRel, excRel]
        refine ⟨targetRes, ?_, topRel⟩
        simpa [evaluateProgWithClock, t, initial, putOracle, insertOracleState, targetFfi] using
          congrArg (fun p : State F × Result (SemEnv Value) Value => (p.1.ffi, p.2)) inserted
end Flapjack.Compiler.Backend.SourceEval.Proofs

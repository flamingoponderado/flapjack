import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleExtractSuccessor

/-! Initial and successive extracted compiler-oracle properties. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.AstHOL
open Flapjack.EvaluateHOL Flapjack.NamespaceHOL Flapjack.SemanticsHOL

/-- The extracted initial oracle has the compiler's initial state and its
successive entries are connected by compiler steps. The evaluator inherits the
rational-cut real-number assumption. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "get_oracle_props"]
theorem get_oracle_props {Config F : Type} (env : SemEnv Value) (s : State F)
    (ci : CompilerInstance Config) (decs : List Dec)
    (premises : nsAll (fun _ value => concreteValue value = true) env.v ∧ s.refs = [] ∧
      s.evalState = some (mkInitEvalState ci) ∧ ¬ semanticsProg s env decs .fail) :
    (∀ r, getOracle ci s env decs 0 = some r → r.2.1 = ci.configV ci.initState) ∧
    (∀ i r', getOracle ci s env decs (i + 1) = some r' →
      ∃ r x, getOracle ci s env decs i = some r ∧ mkCompilerFunFromCi ci r = some x ∧ r'.2.1 = x.1) := by
  obtain ⟨concrete, emptyRefs, initialEval, noFail⟩ := premises
  let recorded : EvalOracleState := ⟨fun _ => ((0, 0), ci.configV ci.initState, []),
    doEvalRecord ci, [[]], 0⟩
  let t : State F := { s with evalState := some (.evalOracle recorded) }
  have relation : stateRel ci s t := by
    refine ⟨⟨mkCompilerFunFromCi ci, ci.configV ci.initState, (0, 0, 1), vFunAbs ci.decsDom ci.decsV⟩,
      recorded, [], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp [t, recorded, emptyRefs, initialEval, mkInitEvalState, recordedOracleWellFormed, Flapjack.holEl, Flapjack.holHd]
  constructor
  · intro r found
    apply extract_oracle_0_st t env decs r s ci
    exact ⟨by simpa [getOracle, t, recorded] using found, noFail, relation, concrete⟩
  · intro i r' found
    have successor : (extractOracle t env decs (i + 1)).isSome := by
      simp [← show getOracle ci s env decs (i + 1) = extractOracle t env decs (i + 1) by rfl, found]
    obtain ⟨r, next, x, nextEq, prevEq, compiled, eq⟩ :=
      extract_oracle_SUC_st t env decs i ci s ⟨successor, relation, concrete, noFail⟩
    have expected : next = r' := by
      apply Option.some.inj
      exact nextEq.symm.trans (by simpa [getOracle, t, recorded] using found)
    subst next
    exact ⟨r, x, by simpa [getOracle, t, recorded] using prevEq, compiled, eq⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationHandle
public import Flapjack.EvaluateProps.Length

@[expose] public section

/-! Match-expression case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Match expressions preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Mat {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp)
    (rows : List (Pat × Flapjack.AstHOL.Exp))
    (ih : (∀ middle outcome values, evaluate s env [expr] = (middle, outcome) ∧
       outcome = .val values ∧ canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true →
       MatchSimAt ci middle env (headValue values) rows bindExnV) ∧ ExpsSimAt (A := A) ci s env [expr]) :
    ExpsSimAt (A := A) ci s env [.mat expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases subRun : evaluate s env [expr] with
  | mk middle subResult =>
    cases subResult with
    | err err =>
      simp only [subRun] at run
      cases run
      have subSafe : Result.err err ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        exprIH s' (.err err) es t env' ⟨subRun, related, envRelated, subSafe⟩
      cases r₁ with
      | val values => cases resultRel₁
      | err targetErr =>
        refine ⟨es₁, t₁, .err targetErr, ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        rw [evaluate, (fixClockEvaluate t env' [expr] []).1, targetRun]
    | val values =>
      simp only [subRun] at run
      by_cases canMatch : canPmatchAll env.c middle.refs (rows.map Prod.fst) (headValue values) = true
      · simp only [canMatch, ↓reduceIte] at run
        obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd₁, stack₁⟩ :=
          exprIH middle (.val values) es t env' ⟨subRun, related, envRelated, by simp⟩
        cases r₁ with
        | err err => cases resultRel₁
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRel es₁) values targetValues := resultRel₁
          obtain ⟨head, valuesEq⟩ := Flapjack.EvaluateProps.evaluateSingFull s env expr middle values subRun
          subst values
          cases valuesRel with
          | @cons _ targetHead _ _ headRel tailRel =>
            cases tailRel with
            | nil =>
              have envRelated₁ : envRel (ValueRel es₁) env env' :=
                (forwardRules (oracleState t.evalState) (.conv none []) (.conv none []) es₁ [] [] env env').2.2.1
                  ⟨envRelated, fwd₁⟩
              have targetMatch : canPmatchAll env'.c t₁.refs (rows.map Prod.fst) (headValue [targetHead]) = true :=
                canPmatchAll_rel env middle (rows.map Prod.fst) (headValue [head]) ci t₁ env' (headValue [targetHead])
                  ⟨canMatch, stateRel₁, by simpa [esEq] using envRelated₁,
                    by simpa [esEq, headValue, Flapjack.holHd] using headRel⟩
              have bindRel : ValueRel es₁ bindExnV bindExnV := .con .nil
              obtain ⟨es₂, t₂, r₂, matchRun, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                matchIH middle (.val [head]) [head] ⟨subRun, rfl, canMatch⟩
                  s' res es₁ t₁ env' (headValue [targetHead]) bindExnV
                  ⟨run, stateRel₁, esEq, envRelated₁, by simpa [headValue, Flapjack.holHd] using headRel,
                    bindRel, safe⟩
              refine ⟨es₂, t₂, r₂, ?_, stateRel₂, esEq₂, resultRel₂, ?_, ?_⟩
              · rw [evaluate, (fixClockEvaluate t env' [expr] []).1, targetRun]
                simp [targetMatch, matchRun]
              · exact envStoreForward_trans _ _ _ ⟨fwd₁, fwd₂⟩
              · intro notAbort
                exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), stack₂ notAbort⟩
      · simp [canMatch, typeError] at run
        obtain ⟨_, rfl⟩ := run
        exact (safe rfl).elim
end Flapjack.Compiler.Backend.SourceEval.Proofs

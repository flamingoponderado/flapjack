module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationCons
public import Flapjack.Compiler.Backend.SourceEval.Proofs.PatternMatchSafety

@[expose] public section

/-! Exception-handler case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Flapjack induction infrastructure with no separate HOL declaration: the match conjunct of the mutual simulation. -/
def MatchSimAt {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (x : Value) (rows : List (Pat × Flapjack.AstHOL.Exp)) (err : Value) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value) (es : EvalOracleState)
    (t : State F) (env' : SemEnv Value) (y err' : Value),
    evaluateMatch s env x rows err = (s', res) ∧ stateRel ci s t ∧ es = oracleState t.evalState ∧
      envRel (ValueRel es) env env' ∧ ValueRel es x y ∧ ValueRel es err err' ∧
      res ≠ .err (.abort .typeError) →
    ∃ es' t' res', evaluateMatch t env' y rows err' = (t', res') ∧ stateRel ci s' t' ∧
      es' = oracleState t'.evalState ∧ resultRel (List.Forall₂ (ValueRel es')) (ValueRel es') res res' ∧
      envStoreForward es es' ∧ (¬ abort res' → envStackForward es es')

/-- Exception handlers preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Handle {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp)
    (rows : List (Pat × Flapjack.AstHOL.Exp))
    (ih : (∀ middle outcome err value, evaluate s env [expr] = (middle, outcome) ∧
       outcome = .err err ∧ err = .raise value ∧
       canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true →
       MatchSimAt ci middle env value rows value) ∧ ExpsSimAt ci s env [expr]) :
    ExpsSimAt ci s env [.handle expr rows] := by
  obtain ⟨matchIH, exprIH⟩ := ih
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  rw [evaluate, (fixClockEvaluate s env [expr] []).1] at run
  cases subRun : evaluate s env [expr] with
  | mk middle subResult =>
    cases subResult with
    | val values =>
      simp only [subRun] at run
      cases run
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        exprIH s' (.val values) t env' ⟨subRun, related, envRelated, by simp⟩
      cases r₁ with
      | err err => cases resultRel₁
      | val targetValues =>
        refine ⟨es₁, t₁, .val targetValues, ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        rw [evaluate, (fixClockEvaluate t env' [expr] []).1, targetRun]
    | err err =>
      cases err with
      | abort why =>
        simp only [subRun] at run
        cases run
        have subSafe : Result.err (.abort why) ≠ .err (.abort .typeError) := safe
        obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
          exprIH s' (.err (.abort why)) t env' ⟨subRun, related, envRelated, subSafe⟩
        cases r₁ with
        | val values => cases resultRel₁
        | err targetErr =>
          cases targetErr with
          | raise value => cases resultRel₁
          | abort why' =>
            change why = why' at resultRel₁
            subst why'
            refine ⟨es₁, t₁, .err (.abort why), ?_, stateRel₁, esEq, rfl, fwd, stack⟩
            rw [evaluate, (fixClockEvaluate t env' [expr] []).1, targetRun]
      | raise value =>
        simp only [subRun] at run
        by_cases canMatch : canPmatchAll env.c middle.refs (rows.map Prod.fst) value = true
        · simp only [canMatch, ↓reduceIte] at run
          obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd₁, stack₁⟩ :=
            exprIH middle (.err (.raise value)) t env' ⟨subRun, related, envRelated, by simp⟩
          cases r₁ with
          | val values => cases resultRel₁
          | err targetErr =>
            cases targetErr with
            | abort why => cases resultRel₁
            | raise targetValue =>
              have valueRel : ValueRel es₁ value targetValue := resultRel₁
              have envRelated₁ : envRel (ValueRel es₁) env env' :=
                (forwardRules (oracleState t.evalState) (.conv none []) (.conv none []) es₁ [] [] env env').2.2.1
                  ⟨envRelated, fwd₁⟩
              have targetMatch : canPmatchAll env'.c t₁.refs (rows.map Prod.fst) targetValue = true :=
                canPmatchAll_rel env middle (rows.map Prod.fst) value ci t₁ env' targetValue
                  ⟨canMatch, stateRel₁, by simpa [esEq] using envRelated₁,
                    by simpa [esEq] using valueRel⟩
              obtain ⟨es₂, t₂, r₂, matchRun, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                matchIH middle (.err (.raise value)) (.raise value) value ⟨subRun, rfl, rfl, canMatch⟩
                  s' res es₁ t₁ env' targetValue targetValue
                  ⟨run, stateRel₁, esEq, envRelated₁, valueRel, valueRel, safe⟩
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

module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDeclarations
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentAppend
public import Flapjack.EvaluateHOL.ClockFull

@[expose] public section

/-! Declaration-list sequencing in the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Declaration-list sequencing preserves the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_DecsCons {Config F : Type} (ci : CompilerInstance Config) (s : State F) (env : SemEnv Value)
    (first second : Dec) (rest : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env [first] = (middle, outcome) ∧
      outcome = .val inner → DecsSimAt ci middle (extendDecEnv inner env) (second :: rest)) ∧
      DecsSimAt ci s env [first]) : DecsSimAt ci s env (first :: second :: rest) := by
  obtain ⟨tailIH, firstIH⟩ := ih
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  rw [evaluateDecsConsSource] at run
  cases firstRun : evaluateDecs s env [first] with
  | mk middle firstResult =>
    cases firstResult with
    | err error =>
      simp only [firstRun] at run
      cases run
      have firstSafe : Result.err error ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetFirst, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        firstIH s' (.err error) t env' ⟨firstRun, related, envRelated, firstSafe⟩
      cases r₁ with
      | val val => cases resultRel₁
      | err targetErr =>
        refine ⟨es₁, t₁, .err targetErr, ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        simp [evaluateDecsConsSource, targetFirst]
    | val inner =>
      simp only [firstRun] at run
      obtain ⟨es₁, t₁, r₁, targetFirst, stateRel₁, esEq, resultRel₁, fwd₁, stack₁⟩ :=
        firstIH middle (.val inner) t env' ⟨firstRun, related, envRelated, by simp⟩
      cases r₁ with
      | err error => cases resultRel₁
      | val inner' =>
        have innerRel : envRel (ValueRel es₁) inner inner' := resultRel₁
        have envRelated₁ : envRel (ValueRel es₁) env env' :=
          (forwardRules (oracleState t.evalState) (.conv none []) (.conv none []) es₁ [] [] env env').2.2.1
            ⟨envRelated, fwd₁⟩
        have extended : envRel (ValueRel es₁) (extendDecEnv inner env) (extendDecEnv inner' env') :=
          envRel_extendDecEnv _ inner inner' env env' ⟨innerRel, envRelated₁⟩
        cases tailRun : evaluateDecs middle (extendDecEnv inner env) (second :: rest) with
        | mk last tailResult =>
          cases tailResult with
          | err error =>
            simp only [tailRun, combineDecResult] at run
            cases run
            obtain ⟨es₂, t₂, r₂, targetTail, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
              tailIH middle (.val inner) inner ⟨firstRun, rfl⟩ s' (.err error) t₁ (extendDecEnv inner' env')
                ⟨tailRun, stateRel₁, by simpa [esEq] using extended, safe⟩
            cases r₂ with
            | val env => cases resultRel₂
            | err targetErr =>
              refine ⟨es₂, t₂, .err targetErr, ?_, stateRel₂, esEq₂, resultRel₂, ?_, ?_⟩
              · simp [evaluateDecsConsSource, targetFirst, targetTail, combineDecResult]
              · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq] using fwd₂⟩
              · intro notAbort
                exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq] using stack₂ notAbort⟩
          | val tailEnv =>
            simp only [tailRun, combineDecResult] at run
            cases run
            obtain ⟨es₂, t₂, r₂, targetTail, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
              tailIH middle (.val inner) inner ⟨firstRun, rfl⟩ s' (.val tailEnv) t₁ (extendDecEnv inner' env')
                ⟨tailRun, stateRel₁, by simpa [esEq] using extended, by simp⟩
            cases r₂ with
            | err error => cases resultRel₂
            | val tailEnv' =>
              refine ⟨es₂, t₂, .val (extendDecEnv tailEnv' inner'), ?_, stateRel₂, esEq₂, ?_, ?_, ?_⟩
              · simp [evaluateDecsConsSource, targetFirst, targetTail, combineDecResult]
                rfl
              · have innerRel₂ : envRel (ValueRel es₂) inner inner' :=
                  (forwardRules es₁ (.conv none []) (.conv none []) es₂ [] [] inner inner').2.2.1
                    ⟨innerRel, by simpa [esEq] using fwd₂⟩
                exact envRel_extendDecEnv _ tailEnv tailEnv' inner inner' ⟨resultRel₂, innerRel₂⟩
              · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq] using fwd₂⟩
              · intro _
                exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq] using stack₂ (by simp [abort])⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

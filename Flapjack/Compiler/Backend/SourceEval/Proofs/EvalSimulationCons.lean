module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationBase
public import Flapjack.EvaluateHOL.ClockFull
public import Flapjack.EvaluateProps.Length

@[expose] public section

/-! Expression-list sequencing in the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Flapjack induction infrastructure with no separate HOL declaration: the expression conjunct of the mutual simulation. -/
def ExpsSimAt {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (exps : List Flapjack.AstHOL.Exp) : Prop :=
  ∀ (s' : State F) (res : Result (List Value) Value) (t : State F) (env' : SemEnv Value),
    evaluate s env exps = (s', res) ∧ stateRel ci s t ∧
      envRel (ValueRel (oracleState t.evalState)) env env' ∧ res ≠ .err (.abort .typeError) →
    ∃ es' t' res', evaluate t env' exps = (t', res') ∧ stateRel ci s' t' ∧
      es' = oracleState t'.evalState ∧ resultRel (List.Forall₂ (ValueRel es')) (ValueRel es') res res' ∧
      envStoreForward (oracleState t.evalState) es' ∧
      (¬ abort res' → envStackForward (oracleState t.evalState) es')

/-- Flapjack induction infrastructure with no separate HOL declaration: the declaration conjunct of the mutual simulation. -/
def DecsSimAt {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (decs : List Dec) : Prop :=
  ∀ (s' : State F) (res : Result (SemEnv Value) Value) (t : State F) (env' : SemEnv Value),
    evaluateDecs s env decs = (s', res) ∧ stateRel ci s t ∧
      envRel (ValueRel (oracleState t.evalState)) env env' ∧ res ≠ .err (.abort .typeError) →
    ∃ es' t' res', evaluateDecs t env' decs = (t', res') ∧ stateRel ci s' t' ∧
      es' = oracleState t'.evalState ∧ resultRel (envRel (ValueRel es')) (ValueRel es') res res' ∧
      envStoreForward (oracleState t.evalState) es' ∧ (¬ abort res' → envStackForward (oracleState t.evalState) es')

/-- The expression-list sequencing induction case. `rest` and the independent
unused `es` binder correspond to HOL's two distinct variables named `es`. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_ExpsCons {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (first second : Flapjack.AstHOL.Exp) (rest : List Flapjack.AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values → ExpsSimAt ci middle env (second :: rest)) ∧
      ExpsSimAt ci s env [first]) :
    ExpsSimAt ci s env (first :: second :: rest) := by
  obtain ⟨restIH, firstIH⟩ := ih
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  rw [evaluateConsSource] at run
  cases firstRun : evaluate s env [first] with
  | mk middle firstResult =>
    cases firstResult with
    | err error =>
      simp only [firstRun] at run
      cases run
      have firstSafe : Result.err error ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetFirst, rel₁, esEq, result₁, fwd₁, stack₁⟩ :=
        firstIH s' (.err error) t env' ⟨firstRun, related, envRelated, firstSafe⟩
      cases r₁ with
      | val vals => cases result₁
      | err err' =>
        refine ⟨es₁, t₁, .err err', ?_, rel₁, esEq, result₁, fwd₁, stack₁⟩
        simp [evaluateConsSource, targetFirst]
    | val values =>
      have firstSafe : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨es₁, t₁, r₁, targetFirst, rel₁, esEq, result₁, fwd₁, stack₁⟩ :=
        firstIH middle (.val values) t env' ⟨firstRun, related, envRelated, firstSafe⟩
      cases r₁ with
      | err err => cases result₁
      | val targetValues =>
        have valuesRelated : List.Forall₂ (ValueRel es₁) values targetValues := result₁
        have envRelated₁ : envRel (ValueRel es₁) env env' :=
          (forwardRules (oracleState t.evalState) (.conv none []) (.conv none []) es₁ [] [] env env').2.2.1
            ⟨envRelated, fwd₁⟩
        have stackFirst : envStackForward (oracleState t.evalState) es₁ := stack₁ (by simp [abort])
        have ⟨head, valuesEq⟩ := Flapjack.EvaluateProps.evaluateSingFull s env first middle values firstRun
        subst values
        cases valuesRelated with
        | @cons _ targetHead _ _ headRel tailRel =>
          cases tailRel with
          | nil =>
            simp only [firstRun] at run
            cases tailRun : evaluate middle env (second :: rest) with
            | mk last tailResult =>
              cases tailResult with
              | err error =>
                simp only [tailRun] at run
                cases run
                obtain ⟨es₂, t₂, r₂, targetTail, rel₂, esEq₂, result₂, fwd₂, stack₂⟩ :=
                  restIH middle (.val [head]) [head] ⟨firstRun, rfl⟩ s' (.err error) t₁ env'
                    ⟨tailRun, rel₁, by simpa [esEq] using envRelated₁, safe⟩
                cases r₂ with
                | val vals => cases result₂
                | err err' =>
                  refine ⟨es₂, t₂, .err err', ?_, rel₂, esEq₂, result₂, ?_, ?_⟩
                  · simp [evaluateConsSource, targetFirst, targetTail]
                  · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq] using fwd₂⟩
                  · intro notAbort
                    exact envStackForward_trans _ _ _ ⟨stackFirst, by simpa [esEq] using stack₂ notAbort⟩
              | val values₂ =>
                simp only [tailRun] at run
                cases run
                obtain ⟨es₂, t₂, r₂, targetTail, rel₂, esEq₂, result₂, fwd₂, stack₂⟩ :=
                  restIH middle (.val [head]) [head] ⟨firstRun, rfl⟩ s' (.val values₂) t₁ env'
                    ⟨tailRun, rel₁, by simpa [esEq] using envRelated₁, by simp⟩
                cases r₂ with
                | err err => cases result₂
                | val targetTailValues =>
                  refine ⟨es₂, t₂, .val (targetHead :: targetTailValues), ?_, rel₂,
                    esEq₂, ?_, ?_, ?_⟩
                  · simp [evaluateConsSource, targetFirst, targetTail, headValue, Flapjack.holHd]
                  · change List.Forall₂ (ValueRel es₂) (headValue [head] :: values₂)
                      (targetHead :: targetTailValues)
                    apply List.Forall₂.cons
                    · simpa [headValue, Flapjack.holHd] using valueRel_forward es₁ es₂ head targetHead headRel
                        (by simpa [esEq] using fwd₂)
                    · exact result₂
                  · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq] using fwd₂⟩
                  · intro notAbort
                    exact envStackForward_trans _ _ _ ⟨stackFirst, by simpa [esEq] using stack₂ (by simp [abort])⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

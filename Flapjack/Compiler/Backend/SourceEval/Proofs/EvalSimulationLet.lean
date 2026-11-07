import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationCons
import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentBind
import Flapjack.EvaluateProps.Length

/-! Let-expression case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Let expressions preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Let {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : Option VarN)
    (bound body : Flapjack.AstHOL.Exp)
    (ih : (∀ middle outcome values, evaluate s env [bound] = (middle, outcome) ∧ outcome = .val values →
      ExpsSimAt (A := A) ci middle { env with v := nsOptBind name (headValue values) env.v } [body]) ∧
      ExpsSimAt (A := A) ci s env [bound]) :
    ExpsSimAt (A := A) ci s env [.let_ name bound body] := by
  obtain ⟨bodyIH, boundIH⟩ := ih
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  rw [evaluate, (fixClockEvaluate s env [bound] []).1] at run
  cases boundRun : evaluate s env [bound] with
  | mk middle boundResult =>
    cases boundResult with
    | err error =>
      simp only [boundRun] at run
      cases run
      have boundSafe : Result.err error ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        boundIH s' (.err error) es t env' ⟨boundRun, related, envRelated, boundSafe⟩
      cases r₁ with
      | val values => cases resultRel₁
      | err targetErr =>
        refine ⟨es₁, t₁, .err targetErr, ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        rw [evaluate, (fixClockEvaluate t env' [bound] []).1, targetRun]
    | val values =>
      simp only [boundRun] at run
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd₁, stack₁⟩ :=
        boundIH middle (.val values) es t env' ⟨boundRun, related, envRelated, by simp⟩
      cases r₁ with
      | err error => cases resultRel₁
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRel es₁) values targetValues := resultRel₁
        obtain ⟨head, valuesEq⟩ := Flapjack.EvaluateProps.evaluateSingFull s env bound middle values boundRun
        subst values
        cases valuesRel with
        | @cons _ targetHead _ _ headRel tailRel =>
          cases tailRel with
          | nil =>
            have envRelated₁ : envRel (ValueRel es₁) env env' :=
              (forwardRules (oracleState t.evalState) (.conv none []) (.conv none []) es₁ [] [] env env').2.2.1
                ⟨envRelated, fwd₁⟩
            have extended : envRel (ValueRel es₁)
                { env with v := nsOptBind name (headValue [head]) env.v }
                { env' with v := nsOptBind name (headValue [targetHead]) env'.v } := by
              cases name with
              | none => simpa [nsOptBind] using envRelated₁
              | some name =>
                simpa [nsOptBind, headValue, Flapjack.holHd] using
                  envRel_add_nsBind (ValueRel es₁) env env.v env' env'.v head targetHead name ⟨envRelated₁, headRel⟩
            obtain ⟨es₂, t₂, r₂, bodyRun, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
              bodyIH middle (.val [head]) [head] ⟨boundRun, rfl⟩ s' res es t₁
                { env' with v := nsOptBind name (headValue [targetHead]) env'.v }
                ⟨run, stateRel₁, by simpa [esEq] using extended, safe⟩
            refine ⟨es₂, t₂, r₂, ?_, stateRel₂, esEq₂, resultRel₂, ?_, ?_⟩
            · rw [evaluate, (fixClockEvaluate t env' [bound] []).1, targetRun]
              exact bodyRun
            · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq] using fwd₂⟩
            · intro notAbort
              exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq] using stack₂ notAbort⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

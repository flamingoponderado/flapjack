import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationCons
import Flapjack.Compiler.Backend.SourceEval.Proofs.ValueRelationSimps
import Flapjack.EvaluateProps.Length
import Flapjack.SemanticPrimitivesHOL.Control

/-! Conditional-expression case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Conditional expressions preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_If {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (cond yes no : Flapjack.AstHOL.Exp)
    (ih : (∀ middle outcome values branch, evaluate s env [cond] = (middle, outcome) ∧
      outcome = .val values ∧ doIf (headValue values) yes no = some branch →
      ExpsSimAt (A := A) ci middle env [branch]) ∧ ExpsSimAt (A := A) ci s env [cond]) :
    ExpsSimAt (A := A) ci s env [.if_ cond yes no] := by
  obtain ⟨branchIH, condIH⟩ := ih
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  rw [evaluate, (fixClockEvaluate s env [cond] []).1] at run
  cases condRun : evaluate s env [cond] with
  | mk middle condResult =>
    cases condResult with
    | err error =>
      simp only [condRun] at run
      cases run
      have condSafe : Result.err error ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        condIH s' (.err error) es t env' ⟨condRun, related, envRelated, condSafe⟩
      cases r₁ with
      | val values => cases resultRel₁
      | err targetErr =>
        refine ⟨es₁, t₁, .err targetErr, ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        rw [evaluate, (fixClockEvaluate t env' [cond] []).1, targetRun]
    | val values =>
      simp only [condRun] at run
      split at run
      next chosen =>
        simp [typeError] at run
        obtain ⟨_, rfl⟩ := run
        exact (safe rfl).elim
      next branch chosen =>
        obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd₁, stack₁⟩ :=
          condIH middle (.val values) es t env' ⟨condRun, related, envRelated, by simp⟩
        cases r₁ with
        | err err => cases resultRel₁
        | val targetValues =>
          have valuesRel : List.Forall₂ (ValueRel es₁) values targetValues := resultRel₁
          obtain ⟨head, valuesEq⟩ := Flapjack.EvaluateProps.evaluateSingFull s env cond middle values condRun
          subst values
          cases valuesRel with
          | @cons _ targetHead _ _ headRel tailRel =>
            cases tailRel with
            | nil =>
              have chosen' : doIf head yes no = some branch := by simpa [headValue, Flapjack.holHd] using chosen
              obtain ⟨b, headEq, branchEq⟩ := doIf_success_boolean head yes no branch chosen'
              have targetEq : targetHead = boolValue b := (valueRel_bool es₁ b targetHead).mp (by simpa [headEq] using headRel)
              have targetChosen : doIf (headValue [targetHead]) yes no = some branch := by
                simpa [headValue, Flapjack.holHd, targetEq, branchEq] using doIf_boolValue b yes no
              have envRelated₁ : envRel (ValueRel es₁) env env' :=
                (forwardRules (oracleState t.evalState) (.conv none []) (.conv none []) es₁ [] [] env env').2.2.1
                  ⟨envRelated, fwd₁⟩
              obtain ⟨es₂, t₂, r₂, branchRun, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                branchIH middle (.val [head]) [head] branch ⟨condRun, rfl, chosen⟩ s' res es t₁ env'
                  ⟨run, stateRel₁, by simpa [esEq] using envRelated₁, safe⟩
              refine ⟨es₂, t₂, r₂, ?_, stateRel₂, esEq₂, resultRel₂, ?_, ?_⟩
              · rw [evaluate, (fixClockEvaluate t env' [cond] []).1, targetRun]
                dsimp only
                split
                next failed => rw [targetChosen] at failed; contradiction
                next selected selectedEq =>
                  have : selected = branch := Option.some.inj (selectedEq.symm.trans targetChosen)
                  subst selected
                  exact branchRun
              · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq] using fwd₂⟩
              · intro notAbort
                exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq] using stack₂ notAbort⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

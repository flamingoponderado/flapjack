module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationIf

@[expose] public section

/-! Short-circuit Boolean case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Short-circuit Boolean expressions preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Log {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (op : Lop) (first second : Flapjack.AstHOL.Exp)
    (ih : (∀ middle outcome values selection branch, evaluate s env [first] = (middle, outcome) ∧
      outcome = .val values ∧ doLog op (headValue values) second = some selection ∧ selection = .exp branch →
      ExpsSimAt ci middle env [branch]) ∧ ExpsSimAt ci s env [first]) :
    ExpsSimAt ci s env [.log op first second] := by
  obtain ⟨branchIH, firstIH⟩ := ih
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  rw [evaluate, (fixClockEvaluate s env [first] []).1] at run
  cases firstRun : evaluate s env [first] with
  | mk middle firstResult =>
    cases firstResult with
    | err error =>
      simp only [firstRun] at run
      cases run
      have firstSafe : Result.err error ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        firstIH s' (.err error) t env' ⟨firstRun, related, envRelated, firstSafe⟩
      cases r₁ with
      | val values => cases resultRel₁
      | err targetErr =>
        refine ⟨es₁, t₁, .err targetErr, ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        rw [evaluate, (fixClockEvaluate t env' [first] []).1, targetRun]
    | val values =>
      simp only [firstRun] at run
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd₁, stack₁⟩ :=
        firstIH middle (.val values) t env' ⟨firstRun, related, envRelated, by simp⟩
      cases r₁ with
      | err err => cases resultRel₁
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRel es₁) values targetValues := resultRel₁
        obtain ⟨head, valuesEq⟩ := Flapjack.EvaluateProps.evaluateSingFull s env first middle values firstRun
        subst values
        cases valuesRel with
        | @cons _ targetHead _ _ headRel tailRel =>
          cases tailRel with
          | nil =>
            split at run
            next failed =>
              simp [typeError] at run
              obtain ⟨_, rfl⟩ := run
              exact (safe rfl).elim
            next value chosen =>
              have chosen' : doLog op head second = some (.val value) := by
                simpa [headValue, Flapjack.holHd] using chosen
              obtain ⟨b, headEq⟩ := doLog_success_boolean op head second (.val value) chosen'
              have targetEq : targetHead = boolValue b := (valueRel_bool es₁ b targetHead).mp (by simpa [headEq] using headRel)
              have valueEq : value = boolValue b := by
                rw [headEq] at chosen'
                cases op <;> cases b <;> cases chosen' <;> rfl
              have targetChosen : doLog op (headValue [targetHead]) second = some (.val value) := by
                simpa [headValue, Flapjack.holHd, targetEq, headEq] using chosen'
              cases run
              refine ⟨es₁, t₁, .val [value], ?_, stateRel₁, esEq, ?_, fwd₁, ?_⟩
              · rw [evaluate, (fixClockEvaluate t env' [first] []).1, targetRun]
                dsimp only
                split
                next failed => rw [targetChosen] at failed; contradiction
                next selected selectedEq =>
                  have equal := Option.some.inj (selectedEq.symm.trans targetChosen)
                  cases equal
                  rfl
                next selected selectedEq =>
                  have equal := Option.some.inj (selectedEq.symm.trans targetChosen)
                  cases equal
              · exact List.Forall₂.cons (by simpa [valueEq] using (valueRel_bool es₁ b (boolValue b)).mpr rfl) .nil
              · intro _
                exact stack₁ (by simp [abort])
            next branch chosen =>
              have chosen' : doLog op head second = some (.exp branch) := by
                simpa [headValue, Flapjack.holHd] using chosen
              obtain ⟨b, headEq⟩ := doLog_success_boolean op head second (.exp branch) chosen'
              have targetEq : targetHead = boolValue b := (valueRel_bool es₁ b targetHead).mp (by simpa [headEq] using headRel)
              have targetChosen : doLog op (headValue [targetHead]) second = some (.exp branch) := by
                simpa [headValue, Flapjack.holHd, targetEq, headEq] using chosen'
              have envRelated₁ : envRel (ValueRel es₁) env env' :=
                (forwardRules (oracleState t.evalState) (.conv none []) (.conv none []) es₁ [] [] env env').2.2.1
                  ⟨envRelated, fwd₁⟩
              obtain ⟨es₂, t₂, r₂, branchRun, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
                branchIH middle (.val [head]) [head] (.exp branch) branch
                  ⟨firstRun, rfl, chosen, rfl⟩ s' res t₁ env'
                  ⟨run, stateRel₁, by simpa [esEq] using envRelated₁, safe⟩
              refine ⟨es₂, t₂, r₂, ?_, stateRel₂, esEq₂, resultRel₂, ?_, ?_⟩
              · rw [evaluate, (fixClockEvaluate t env' [first] []).1, targetRun]
                dsimp only
                split
                next failed => rw [targetChosen] at failed; contradiction
                next selected selectedEq =>
                  have equal := Option.some.inj (selectedEq.symm.trans targetChosen)
                  cases equal
                next selected selectedEq =>
                  have equal := Option.some.inj (selectedEq.symm.trans targetChosen)
                  cases equal
                  exact branchRun
              · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq] using fwd₂⟩
              · intro notAbort
                exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq] using stack₂ notAbort⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

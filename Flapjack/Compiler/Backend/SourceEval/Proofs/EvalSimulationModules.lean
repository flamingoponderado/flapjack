import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationDeclarations
import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentLift
import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentAppend
import Flapjack.EvaluateHOL.ClockFull

/-! Module and local declaration cases of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Module declarations preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Dmod {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (name : ModN) (decs : List Dec)
    (ih : DecsSimAt ci s env decs) : DecsSimAt ci s env [.dmod name decs] := by
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  rw [evaluateDecs] at run
  cases innerRun : evaluateDecs s env decs with
  | mk middle innerResult =>
    cases innerResult with
    | err error =>
      simp only [innerRun] at run
      cases run
      have innerSafe : Result.err error ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        ih s' (.err error) t env' ⟨innerRun, related, envRelated, innerSafe⟩
      cases r₁ with
      | val inner => cases resultRel₁
      | err targetErr =>
        refine ⟨es₁, t₁, .err targetErr, ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        simp [evaluateDecs, targetRun]
    | val inner =>
      simp only [innerRun] at run
      cases run
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        ih s' (.val inner) t env' ⟨innerRun, related, envRelated, by simp⟩
      cases r₁ with
      | err err => cases resultRel₁
      | val inner' =>
        have innerRel : envRel (ValueRel es₁) inner inner' := resultRel₁
        refine ⟨es₁, t₁, .val { v := nsLift name inner'.v, c := nsLift name inner'.c },
          ?_, stateRel₁, esEq, ?_, fwd, ?_⟩
        · simp [evaluateDecs, targetRun]
        · exact envRel_nsLift _ inner inner.v inner.c inner' inner'.v inner'.c name innerRel
        · intro _
          exact stack (by simp [abort])

/-- Local declarations preserve the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Dlocal {Config F : Type} (ci : CompilerInstance Config) (s : State F)
    (env : SemEnv Value) (localDecs decs : List Dec)
    (ih : (∀ middle outcome inner, evaluateDecs s env localDecs = (middle, outcome) ∧
      outcome = .val inner → DecsSimAt ci middle (extendDecEnv inner env) decs) ∧
      DecsSimAt ci s env localDecs) : DecsSimAt ci s env [.dlocal localDecs decs] := by
  obtain ⟨bodyIH, localIH⟩ := ih
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  rw [evaluateDecs, (fixClockEvaluate s env [] localDecs).2] at run
  cases localRun : evaluateDecs s env localDecs with
  | mk middle localResult =>
    cases localResult with
    | err error =>
      simp only [localRun] at run
      cases run
      have localSafe : Result.err error ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        localIH s' (.err error) t env' ⟨localRun, related, envRelated, localSafe⟩
      cases r₁ with
      | val inner => cases resultRel₁
      | err targetErr =>
        refine ⟨es₁, t₁, .err targetErr, ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        rw [evaluateDecs, (fixClockEvaluate t env' [] localDecs).2, targetRun]
    | val inner =>
      simp only [localRun] at run
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd₁, stack₁⟩ :=
        localIH middle (.val inner) t env' ⟨localRun, related, envRelated, by simp⟩
      cases r₁ with
      | err err => cases resultRel₁
      | val inner' =>
        have innerRel : envRel (ValueRel es₁) inner inner' := resultRel₁
        have envRelated₁ : envRel (ValueRel es₁) env env' :=
          (forwardRules (oracleState t.evalState) (.conv none []) (.conv none []) es₁ [] [] env env').2.2.1
            ⟨envRelated, fwd₁⟩
        have extended : envRel (ValueRel es₁) (extendDecEnv inner env) (extendDecEnv inner' env') :=
          envRel_extendDecEnv _ inner inner' env env' ⟨innerRel, envRelated₁⟩
        obtain ⟨es₂, t₂, r₂, bodyRun, stateRel₂, esEq₂, resultRel₂, fwd₂, stack₂⟩ :=
          bodyIH middle (.val inner) inner ⟨localRun, rfl⟩ s' res t₁ (extendDecEnv inner' env')
            ⟨run, stateRel₁, by simpa [esEq] using extended, safe⟩
        refine ⟨es₂, t₂, r₂, ?_, stateRel₂, esEq₂, resultRel₂, ?_, ?_⟩
        · rw [evaluateDecs, (fixClockEvaluate t env' [] localDecs).2, targetRun]
          exact bodyRun
        · exact envStoreForward_trans _ _ _ ⟨fwd₁, by simpa [esEq] using fwd₂⟩
        · intro notAbort
          exact envStackForward_trans _ _ _ ⟨stack₁ (by simp [abort]), by simpa [esEq] using stack₂ notAbort⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

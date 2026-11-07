import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationCons
import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentLookup
/-! Source evaluator simulation for basic expressions. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL
/-- Literal expressions preserve the value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Lit {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (lit : Lit) :
    ExpsSimAt (A := A) ci s env [.lit lit] := by
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨oracleState t.evalState, t, .val [.litv lit], ?_, related, rfl, ?_,
    envStoreForward_refl _, fun _ => envStackForward_refl _⟩
  · simp [evaluate]
  · exact List.Forall₂.cons (ValueRel.lit _) List.Forall₂.nil
/-- Raising an exception preserves the simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Raise {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp)
    (ih : ExpsSimAt (A := A) ci s env [expr]) :
    ExpsSimAt (A := A) ci s env [.raise expr] := by
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  rw [evaluate] at run
  cases subRun : evaluate s env [expr] with
  | mk middle subResult =>
    cases subResult with
    | err error =>
      simp only [subRun] at run
      cases run
      have subSafe : Result.err error ≠ .err (.abort .typeError) := safe
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        ih s' (.err error) es t env' ⟨subRun, related, envRelated, subSafe⟩
      cases r₁ with
      | val vals => cases resultRel₁
      | err err' =>
        refine ⟨es₁, t₁, .err err', ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
        simp [evaluate, targetRun]
    | val values =>
      simp only [subRun] at run
      cases run
      obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
        ih s' (.val values) es t env' ⟨subRun, related, envRelated, by simp⟩
      cases r₁ with
      | err err => cases resultRel₁
      | val targetValues =>
        have valuesRel : List.Forall₂ (ValueRel es₁) values targetValues := resultRel₁
        obtain ⟨head, rfl⟩ := Flapjack.EvaluateProps.evaluateSingFull s env expr s' values subRun
        cases valuesRel with
        | @cons _ targetHead _ _ headRel tailRel =>
          cases tailRel with
          | nil =>
            refine ⟨es₁, t₁, .err (.raise targetHead), ?_, stateRel₁, esEq, ?_, fwd, ?_⟩
            · simp [evaluate, targetRun, headValue, Flapjack.holHd]
            · simpa [resultRel, excRel, headValue, Flapjack.holHd] using headRel
            · intro _
              exact stack (by simp [abort])
/-- Variable lookup preserves the value relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Var {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : Flapjack.NamespaceHOL.Ident ModN VarN) :
    ExpsSimAt (A := A) ci s env [.var name] := by
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  cases found : Flapjack.NamespaceHOL.nsLookup env.v name with
  | none =>
    simp [evaluate, found, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
  | some value =>
    simp [evaluate, found] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨value', found', valueRel⟩ :=
      envRel_nsLookup_v (ValueRel (oracleState t.evalState)) env env' name value ⟨envRelated, found⟩
    refine ⟨oracleState t.evalState, t, .val [value'], ?_, related, rfl, ?_,
      envStoreForward_refl _, fun _ => envStackForward_refl _⟩
    · simp [evaluate, found']
    · exact List.Forall₂.cons valueRel List.Forall₂.nil

/-- Function literals preserve the environment relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Fn {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : VarN) (body : Flapjack.AstHOL.Exp) :
    ExpsSimAt (A := A) ci s env [.fn name body] := by
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  simp [evaluate] at run
  obtain ⟨rfl, rfl⟩ := run
  refine ⟨oracleState t.evalState, t, .val [.closure env' name body], ?_, related, rfl, ?_,
    envStoreForward_refl _, fun _ => envStackForward_refl _⟩
  · simp [evaluate]
  · exact List.Forall₂.cons (ValueRel.closure ((valueEnvRel_iff _ _ _).mpr envRelated)) List.Forall₂.nil
/-- Type annotations preserve the expression simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Tannot {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp) (typ : AstT)
    (ih : ExpsSimAt (A := A) ci s env [expr]) :
    ExpsSimAt (A := A) ci s env [.tannot expr typ] := by
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
    ih s' res es t env' ⟨by simpa [evaluate] using run, related, envRelated, safe⟩
  exact ⟨es₁, t₁, r₁, by simpa [evaluate] using targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩

/-- Location annotations preserve the expression simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Lannot {Config F A : Type} [Nonempty A] (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (expr : Flapjack.AstHOL.Exp) (loc : Flapjack.Misc.Location.Locs)
    (ih : ExpsSimAt (A := A) ci s env [expr]) :
    ExpsSimAt (A := A) ci s env [.lannot expr loc] := by
  intro s' res es t env' ⟨run, related, envRelated, safe⟩
  obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
    ih s' res es t env' ⟨by simpa [evaluate] using run, related, envRelated, safe⟩
  exact ⟨es₁, t₁, r₁, by simpa [evaluate] using targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

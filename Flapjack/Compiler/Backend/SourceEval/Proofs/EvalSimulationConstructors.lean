module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.EvalSimulationCons
public import Flapjack.Compiler.Backend.SourceEval.Proofs.EnvironmentConstructors
public import Mathlib.Data.List.Forall2

@[expose] public section

/-! Constructor-expression case of the source evaluator simulation. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.NamespaceHOL Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.EvaluateHOL

/-- Constructor evaluation preserves the source evaluator simulation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "eval_simulation"]
theorem evalSimulation_Con {Config F : Type} (ci : CompilerInstance Config)
    (s : State F) (env : SemEnv Value) (name : Option (Ident ModN ConN))
    (args : List Flapjack.AstHOL.Exp)
    (ih : doConCheck env.c name args.length = true → ExpsSimAt ci s env args.reverse) :
    ExpsSimAt ci s env [.con name args] := by
  intro s' res t env' ⟨run, related, envRelated, safe⟩
  have constructors : env'.c = env.c := envRel_imp_c _ env env' envRelated
  by_cases check : doConCheck env.c name args.length = true
  · have targetCheck : doConCheck env'.c name args.length = true := by simpa [constructors] using check
    rw [evaluate] at run
    simp only [check, ↓reduceIte] at run
    cases subRun : evaluate s env args.reverse with
    | mk middle subResult =>
      cases subResult with
      | err error =>
        simp only [subRun] at run
        cases run
        have subSafe : Result.err error ≠ .err (.abort .typeError) := safe
        obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
          ih check s' (.err error) t env' ⟨subRun, related, envRelated, subSafe⟩
        cases r₁ with
        | val vals => cases resultRel₁
        | err err' =>
          refine ⟨es₁, t₁, .err err', ?_, stateRel₁, esEq, resultRel₁, fwd, stack⟩
          simp [evaluate, targetCheck, targetRun]
      | val values =>
        simp only [subRun] at run
        cases built : buildConv env.c name values.reverse with
        | none =>
          simp [built, typeError] at run
          obtain ⟨_, rfl⟩ := run
          exact (safe rfl).elim
        | some v =>
          simp only [built] at run
          cases run
          obtain ⟨es₁, t₁, r₁, targetRun, stateRel₁, esEq, resultRel₁, fwd, stack⟩ :=
            ih check s' (.val values) t env' ⟨subRun, related, envRelated, by simp⟩
          cases r₁ with
          | err err => cases resultRel₁
          | val values' =>
            have vsRel : List.Forall₂ (ValueRel es₁) values.reverse values'.reverse :=
              (List.forall₂_reverse_iff).2 resultRel₁
            cases name with
            | none =>
              simp [buildConv] at built
              subst v
              refine ⟨es₁, t₁, .val [.conv none values'.reverse], ?_, stateRel₁, esEq, ?_, fwd, ?_⟩
              · simp [evaluate, targetCheck, targetRun, buildConv]
              · exact List.Forall₂.cons (.con vsRel) .nil
              · intro _
                exact stack (by simp [abort])
            | some id =>
              cases found : nsLookup env.c id with
              | none => simp [buildConv, found] at built
              | some info =>
                obtain ⟨arity, stamp⟩ := info
                simp [buildConv, found] at built
                subst v
                refine ⟨es₁, t₁, .val [.conv (some stamp) values'.reverse], ?_,
                  stateRel₁, esEq, ?_, fwd, ?_⟩
                · simp [evaluate, check, targetRun, buildConv, constructors, found]
                · exact List.Forall₂.cons (.con vsRel) .nil
                · intro _
                  exact stack (by simp [abort])
  · simp [evaluate, check, typeError] at run
    obtain ⟨_, rfl⟩ := run
    exact (safe rfl).elim
end Flapjack.Compiler.Backend.SourceEval.Proofs

module

public import Flapjack.Compiler.Backend.SourceEval.Proofs.PatternMatch

@[expose] public section

/-! Matchability under source-evaluator recording. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL

/-- The source pattern-match theorem in the original local rule form. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "pmatch_drule_form"]
theorem pmatchDrule {Config F : Type} (env : SemEnv Value) (s : State F) (p : Pat) (x : Value)
    (result : MatchResult (List (VarN × Value))) (ci : CompilerInstance Config)
    (t : State F) (env' : SemEnv Value) (y : Value)
    (premises : pmatch env.c s.refs p x [] = result ∧ stateRel ci s t ∧
      envRel (ValueRel (oracleState t.evalState)) env env' ∧
      ValueRel (oracleState t.evalState) x y) :
    matchResultRel true (List.Forall₂ (Flapjack.holRprod (· = ·) (ValueRel (oracleState t.evalState))))
      result (pmatch env'.c t.refs p y []) := by
  obtain ⟨run, states, environments, values⟩ := premises
  have simulation := (sourcePmatch ci s t (oracleState t.evalState) env env'
    ⟨states, rfl, environments⟩).1 env.c s.refs p x [] y [] ⟨rfl, rfl, values, .nil⟩
  simpa [run] using simulation

/-- Matchability is preserved by the source evaluator's recording relation. -/
@[hol "cakeml/compiler/backend/proofs/source_evalProofScript.sml" "can_pmatch_all"]
theorem canPmatchAll_rel {Config F : Type} (env : SemEnv Value) (s : State F) (pats : List Pat)
    (x : Value) (ci : CompilerInstance Config) (t : State F) (env' : SemEnv Value) (y : Value)
    (premises : canPmatchAll env.c s.refs pats x = true ∧ stateRel ci s t ∧
      envRel (ValueRel (oracleState t.evalState)) env env' ∧
      ValueRel (oracleState t.evalState) x y) :
    canPmatchAll env'.c t.refs pats y = true := by
  obtain ⟨safe, states, environments, values⟩ := premises
  induction pats with
  | nil => rfl
  | cons p ps ih =>
    simp only [canPmatchAll, List.all_cons, Bool.and_eq_true] at safe
    have related := pmatchDrule env s p x (pmatch env.c s.refs p x []) ci t env' y
      ⟨rfl, states, environments, values⟩
    have rest := ih safe.2
    cases source : pmatch env.c s.refs p x [] with
    | typeError => simp [source] at safe
    | noMatch =>
      have target : pmatch env'.c t.refs p y [] = .noMatch := by
        simpa [source, matchResultRel] using related
      simp only [canPmatchAll, List.all_cons, Bool.and_eq_true, target]
      exact ⟨True.intro, rest⟩
    | «match» bindings =>
      obtain ⟨bindings', target, _⟩ := by simpa [source, matchResultRel] using related
      simp only [canPmatchAll, List.all_cons, Bool.and_eq_true, target]
      exact ⟨True.intro, rest⟩
end Flapjack.Compiler.Backend.SourceEval.Proofs

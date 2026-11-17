module

public import Flapjack.Compiler.Backend.SourceLet.Proofs.Correct
public import Flapjack.SemanticsHOL
public import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleInduction

@[expose] public section

/-! Observable semantics preservation for source let-lifting. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.SemanticsHOL

/-- The source let-lifting pass preserves all original observations of a
program that cannot fail with a type error. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "compile_semantics"]
theorem compile_semantics {F : Type} (state : State F) (env : SemEnv Value)
    (program : List Dec) (outcome : HolBehaviour)
    (premises : ¬ semanticsProg state env program .fail ∧ semanticsProg state env program outcome) :
    semanticsProg state env (compileDecs program) outcome := by
  obtain ⟨noFail, source⟩ := premises
  have observations : ∀ clock, evaluateProgWithClock state env clock (compileDecs program) =
      evaluateProgWithClock state env clock program := by
    intro clock
    cases run : evaluateDecs { state with clock := clock } env program with
    | mk next result =>
      have safe : result ≠ .err (.abort .typeError) := by
        intro bad
        apply noFail
        change ∃ k, (evaluateProgWithClock state env k program).2 = .err (.abort .typeError)
        refine ⟨clock, ?_⟩
        simp [evaluateProgWithClock, run, bad]
      have target := compile_decs_correct { state with clock := clock } env program next result ⟨run, safe⟩
      simp [evaluateProgWithClock, run, target]
  cases outcome <;> simpa only [semanticsProg, observations] using source

/-- Let-lifting preserves observable semantics when composed into an inserted
Eval oracle. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "compile_semantics_oracle"]
theorem compile_semantics_oracle {Config F : Type}
    (ci : SourceEval.Proofs.CompilerInstance Config) (state : State F) (env : SemEnv Value)
    (program : List Dec) (outcome : HolBehaviour) (f : List Dec → List Dec)
    (premises : SourceEval.Proofs.isInsertOracle ci f state.evalState ∧
      ¬ semanticsProg state env program .fail ∧ semanticsProg state env program outcome) :
    semanticsProg { state with evalState := SourceEval.Proofs.adjustOracle ci (compileDecs ∘ f) state.evalState }
      env program outcome := by
  apply SourceEval.Proofs.adjust_oracle_semantics_prog compileDecs f ci ?_ state env program outcome premises
  intro s e ds s' result premises
  exact compile_decs_correct s e ds s' result premises

end Flapjack.Compiler.Backend.SourceLet

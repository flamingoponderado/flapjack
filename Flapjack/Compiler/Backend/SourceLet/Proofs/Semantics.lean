import Flapjack.Compiler.Backend.SourceLet.Proofs.Correct
import Flapjack.SemanticsHOL
import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleInduction

/-! Observable semantics preservation for source let-lifting. -/
namespace Flapjack.Compiler.Backend.SourceLet
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.SemanticsHOL

/-- Non-failing source programs and their lifted versions have the same
clock-indexed observations. This is Flapjack proof infrastructure. -/
theorem compileDecs_clock_observations {F : Type} (state : State F) (env : SemEnv Value)
    (program : List Dec) (noFail : ¬ semanticsProg state env program .fail) (clock : Nat) :
    evaluateProgWithClock state env clock (compileDecs program) =
      evaluateProgWithClock state env clock program := by
  cases run : evaluateDecs { state with clock := clock } env program with
  | mk next result =>
    have safe : result ≠ .err (.abort .typeError) := by
      intro bad
      apply noFail
      change ∃ k, (evaluateProgWithClock state env k program).2 = .err (.abort .typeError)
      refine ⟨clock, ?_⟩
      simp [evaluateProgWithClock, run, bad]
    have target := compile_decs_correct { state with clock := clock } next env program result run safe
    simp [evaluateProgWithClock, run, target]

/-- The source let-lifting pass preserves all original observations of a
program that cannot fail with a type error. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "compile_semantics"]
theorem compile_semantics {F : Type} (state : State F) (env : SemEnv Value)
    (program : List Dec) (outcome : HolBehaviour)
    (noFail : ¬ semanticsProg state env program .fail)
    (source : semanticsProg state env program outcome) :
    semanticsProg state env (compileDecs program) outcome := by
  have observations := compileDecs_clock_observations state env program noFail
  cases outcome <;> simpa only [semanticsProg, observations] using source

/-- Let-lifting preserves observable semantics when composed into an inserted
Eval oracle. Source evaluator and carrier correspondence remain pending review. -/
@[hol "cakeml/compiler/backend/proofs/source_letProofScript.sml" "compile_semantics_oracle"]
theorem compile_semantics_oracle {Config F : Type}
    (ci : SourceEval.Proofs.CompilerInstance Config) (f : List Dec → List Dec)
    (state : State F) (env : SemEnv Value) (program : List Dec) (outcome : HolBehaviour)
    (inserted : SourceEval.Proofs.isInsertOracle ci f state.evalState)
    (noFail : ¬ semanticsProg state env program .fail)
    (source : semanticsProg state env program outcome) :
    semanticsProg { state with evalState := SourceEval.Proofs.adjustOracle ci (compileDecs ∘ f) state.evalState }
      env program outcome := by
  apply SourceEval.Proofs.adjust_oracle_semantics_prog ci f compileDecs ?_ state env program outcome inserted noFail source
  intro s s' e ds result run safe
  exact compile_decs_correct s s' e ds result run safe

end Flapjack.Compiler.Backend.SourceLet

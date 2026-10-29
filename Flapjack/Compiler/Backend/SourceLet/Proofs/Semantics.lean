import Flapjack.Compiler.Backend.SourceLet.Proofs.Correct
import Flapjack.SemanticsHOL

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

end Flapjack.Compiler.Backend.SourceLet

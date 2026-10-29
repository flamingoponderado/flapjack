import Flapjack.Compiler.Backend.SourceEval.Proofs.OracleAdjustment
import Flapjack.SemanticsHOL

/-! Lifting a declaration evaluation simulation to observable program semantics. -/
namespace Flapjack.Compiler.Backend.SourceEval.Proofs
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.EvaluateHOL Flapjack.SemanticsHOL

/-- The declaration component of the oracle-adjusted evaluator simulation.
This Flapjack predicate is proof infrastructure, not a separate HOL definition.
Its proof for the original evaluator remains to be established. -/
def AdjustedDecsSimulation {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) : Prop :=
  ∀ (state next : State F) (env : SemEnv Value) (program : List Dec)
    (result : Result (SemEnv Value) Value),
    evaluateDecs state env program = (next, result) →
    isInsertOracle ci f state.evalState →
    result ≠ .err (.abort .typeError) →
    evaluateDecs { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env program =
      ({ next with evalState := adjustOracle ci (compile ∘ f) next.evalState }, result)

/-- A declaration simulation gives identical clock-indexed FFI observations.
This is Flapjack proof infrastructure; the simulation is still a premise. -/
theorem adjusted_clock_observations {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (simulation : AdjustedDecsSimulation (F := F) ci f compile)
    (state : State F) (env : SemEnv Value) (program : List Dec)
    (inserted : isInsertOracle ci f state.evalState)
    (noFail : ¬ semanticsProg state env program .fail) (clock : Nat) :
    evaluateProgWithClock { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env clock program =
      evaluateProgWithClock state env clock program := by
  cases run : evaluateDecs { state with clock := clock } env program with
  | mk next result =>
    have safe : result ≠ .err (.abort .typeError) := by
      intro bad
      apply noFail
      change ∃ k, (evaluateProgWithClock state env k program).2 = .err (.abort .typeError)
      refine ⟨clock, ?_⟩
      simp [evaluateProgWithClock, run, bad]
    have target := simulation { state with clock := clock } next env program result run inserted safe
    simpa [evaluateProgWithClock, run] using congrArg (fun p => (p.1.ffi, p.2)) target

/-- Conditional observational lifting for all behaviours, including the
divergence trace. This is Flapjack infrastructure: unlike HOL's full theorem,
it assumes the declaration simulation instead of proving it. -/
theorem adjusted_semanticsProg_of_simulation {Config F : Type} (ci : CompilerInstance Config)
    (f compile : List Dec → List Dec) (simulation : AdjustedDecsSimulation (F := F) ci f compile)
    (state : State F) (env : SemEnv Value) (program : List Dec) (outcome : HolBehaviour)
    (inserted : isInsertOracle ci f state.evalState)
    (noFail : ¬ semanticsProg state env program .fail)
    (source : semanticsProg state env program outcome) :
    semanticsProg { state with evalState := adjustOracle ci (compile ∘ f) state.evalState } env program outcome := by
  have observations := adjusted_clock_observations ci f compile simulation state env program inserted noFail
  cases outcome <;> simpa only [semanticsProg, observations] using source

end Flapjack.Compiler.Backend.SourceEval.Proofs

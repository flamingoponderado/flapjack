module

public import Flapjack.Compiler.Backend.Semantics.DataSem.EvaluateClock
public import Lean.Elab.Tactic.Omega

-- Proofs below unfold private helpers of these modules.
import all Flapjack.Compiler.Backend.Semantics.DataSem.Evaluate
@[expose] public section

/-! Execution of compiler-generated tick sequences. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL

/-- A generated tick sequence either consumes its requested clock budget or
times out with cleared locals and stack. The original theorem also uses the
iterated decrement operation; this equivalent subtraction form is untagged
pending evaluator and carrier correspondence review. -/
theorem evaluate_mkTicks {C F : Type} (program : DataLang.Prog) (state : State C F) (ticks : Nat) :
    evaluate (DataLang.mkTicks ticks program) state =
      if state.clock < ticks then
        (some (.err (.abort .timeoutError)),
          { state with clock := 0, locals := .ln, stack := [], localsSize := some 0 })
      else evaluate program { state with clock := state.clock - ticks } := by
  induction ticks generalizing state with
  | zero => simp [DataLang.mkTicks]
  | succ ticks ih =>
    rw [DataLang.mkTicks, evaluate, fixClock_evaluate]
    by_cases zero : state.clock = 0
    · simp [evaluate, zero, flushState]
    · simp only [evaluate, zero, ↓reduceIte]
      rw [ih]
      simp only [decClock]
      by_cases enough : state.clock < ticks + 1
      · have small : state.clock - 1 < ticks := by omega
        simp [enough, small]
      · have enough' : ¬ state.clock - 1 < ticks := by omega
        simp [enough, enough', show state.clock - 1 - ticks = state.clock - (ticks + 1) by omega]

end Flapjack.Compiler.Backend.DataSem

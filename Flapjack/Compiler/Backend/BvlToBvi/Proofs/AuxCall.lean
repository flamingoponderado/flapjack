import Flapjack.Compiler.Backend.BvlToBvi.Proofs.BoundEvaluation
import Flapjack.Compiler.Backend.BviLet.Proofs.Simulation
import Flapjack.Compiler.Backend.Semantics.BviProps.EvaluateClockShift

/-! Execution of the auxiliary call emitted for empty BVL lets. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value findCode)
open Flapjack.SemanticPrimitivesHOL (Result)

/-- An installed optimized auxiliary body executes with one additional call
tick after its arguments. Its result is the relocated BVL-shaped result, which
cannot contain BVI's return exception. Untagged until the BVI evaluator and
dispatcher are reviewed. -/
theorem evaluate_aux_call {C F : Type} (arguments : List Bvi.Exp) (env values : List Value)
    (state middle final : BviSem.BviState C F) (location arity extra : Nat)
    (body : Bvi.Exp) (relocate : Nat → Nat) (result : Result (List Value) Value)
    (argsRun : BviSem.evaluate arguments env state = (.val values, middle))
    (length : values.length = arity)
    (installed : sptLookup location middle.code = some (arity, BviLet.compileSing [] 0 body))
    (bodyRun : BviSem.evaluate [body] values (BviProps.incClock extra middle) =
      (mapSimulationResult relocate result, final))
    (notTypeError : result ≠ .err (.abort .typeError)) :
    BviSem.evaluate [.call 0 (some location) arguments none] env
      (BviProps.incClock (extra + 1) state) = (mapSimulationResult relocate result, final) := by
  have mappedOk : mapSimulationResult relocate result ≠ .err (.abort .typeError) := by
    cases result with
    | val values => simp [mapSimulationResult]
    | err error => cases error <;> simp_all [mapSimulationResult]
  have optimized := BviLet.Proofs.evaluate_compileList [body] values
    (BviProps.incClock extra middle) final (mapSimulationResult relocate result) bodyRun mappedOk
  have optimizedRun : BviSem.evaluate [BviLet.compileSing [] 0 body] values
      (BviProps.incClock extra middle) = (mapSimulationResult relocate result, final) := by
    simpa [BviLet.compileList, BviSem.evaluateTuple] using optimized
  have shifted := BviProps.evaluate_inv_clock arguments env state middle (.val values) (extra + 1)
    argsRun (by simp)
  have found : findCode (some location) values (BviProps.incClock (extra + 1) middle).code =
      some (values, BviLet.compileSing [] 0 body) := by
    simp [BviProps.incClock, findCode, installed, length]
  have enough : ¬ (BviProps.incClock (extra + 1) middle).clock < 0 + 1 := by
    simp [BviProps.incClock]
  have dec : BviSem.decClock 1 (BviProps.incClock (extra + 1) middle) =
      BviProps.incClock extra middle := by
    cases middle
    simp only [BviSem.decClock, BviProps.incClock]
    congr 1
  rw [BviSem.evaluate]
  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [BviSem.fixClock_evaluate, shifted]
  simp only
  rw [found]
  simp only [enough, ↓reduceIte, dec]
  rw [BviSem.fixClock_evaluate, optimizedRun]
  cases result with
  | val values => rfl
  | err error => cases error <;> rfl

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

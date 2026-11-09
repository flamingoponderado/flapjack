import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileEmptyLet

/-! Auxiliary calls with an exception handler. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value findCode)
open Flapjack.SemanticPrimitivesHOL (Result)

/-- A successful auxiliary body or non-raising failure bypasses the installed
handler. Untagged pending BVI evaluator and dispatcher review. -/
theorem evaluate_aux_call_handle_noRaise {C F : Type} (arguments : List Bvi.Exp)
    (env values : List Value) (state middle final : BviSem.BviState C F)
    (location arity extra : Nat) (body handler : Bvi.Exp)
    (relocate : Nat → Nat) (result : Result (List Value) Value)
    (argsRun : BviSem.evaluate arguments env state = (.val values, middle))
    (length : values.length = arity)
    (installed : sptLookup location middle.code = some (arity, BviLet.compileSing [] 0 body))
    (bodyRun : BviSem.evaluate [body] values (BviProps.incClock extra middle) =
      (mapSimulationResult relocate result, final))
    (notTypeError : result ≠ .err (.abort .typeError))
    (noRaise : ∀ value, result ≠ .err (.raise value)) :
    BviSem.evaluate [.call 0 (some location) arguments (some handler)] env
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
  | err error =>
    cases error with
    | abort reason => rfl
    | raise value => exact False.elim (noRaise value rfl)

/-- A raised exception from installed auxiliary code reaches the compiled
handler with the original outer environment. The clock allowances cover the
argument, body and handler evaluations plus the call tick. Untagged pending
BVI evaluator and dispatcher review. -/
theorem evaluate_aux_call_handle_raise {C F : Type} (arguments : List Bvi.Exp)
    (env values : List Value) (state middle bodyState final : BviSem.BviState C F)
    (location arity bodyClock handlerClock : Nat) (body handler : Bvi.Exp) (exception : Value)
    (relocate : Nat → Nat) (result : Result (List Value) Value)
    (argsRun : BviSem.evaluate arguments env state = (.val values, middle))
    (length : values.length = arity)
    (installed : sptLookup location middle.code = some (arity, BviLet.compileSing [] 0 body))
    (bodyRun : BviSem.evaluate [body] values (BviProps.incClock bodyClock middle) =
      (.err (.raise (.exn exception)), bodyState))
    (handlerRun : BviSem.evaluate [handler] (exception :: env) (BviProps.incClock handlerClock bodyState) =
      (mapSimulationResult relocate result, final)) :
    BviSem.evaluate [.call 0 (some location) arguments (some handler)] env
      (BviProps.incClock (handlerClock + bodyClock + 1) state) = (mapSimulationResult relocate result, final) := by
  have optimized := BviLet.Proofs.evaluate_compileList [body] values
    (BviProps.incClock bodyClock middle) bodyState (.err (.raise (.exn exception))) bodyRun (by simp)
  have optimizedRun : BviSem.evaluate [BviLet.compileSing [] 0 body] values
      (BviProps.incClock bodyClock middle) = (.err (.raise (.exn exception)), bodyState) := by
    simpa [BviLet.compileList, BviSem.evaluateTuple] using optimized
  have shiftedBody := BviProps.evaluate_inv_clock [BviLet.compileSing [] 0 body] values
    (BviProps.incClock bodyClock middle) bodyState (.err (.raise (.exn exception))) handlerClock
    optimizedRun (by simp)
  rw [BviProps.incClock_add] at shiftedBody
  have shiftedArgs := BviProps.evaluate_inv_clock arguments env state middle (.val values)
    (handlerClock + bodyClock + 1) argsRun (by simp)
  have found : findCode (some location) values (BviProps.incClock (handlerClock + bodyClock + 1) middle).code =
      some (values, BviLet.compileSing [] 0 body) := by
    simp [BviProps.incClock, findCode, installed, length]
  have enough : ¬ (BviProps.incClock (handlerClock + bodyClock + 1) middle).clock < 0 + 1 := by
    simp [BviProps.incClock]
  have dec : BviSem.decClock 1 (BviProps.incClock (handlerClock + bodyClock + 1) middle) =
      BviProps.incClock (handlerClock + bodyClock) middle := by
    cases middle
    simp only [BviSem.decClock, BviProps.incClock]
    congr 1
  rw [BviSem.evaluate]
  simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  rw [BviSem.fixClock_evaluate, shiftedArgs]
  simp only
  rw [found]
  simp only [enough, ↓reduceIte, dec]
  rw [BviSem.fixClock_evaluate, shiftedBody]
  dsimp only
  rw [handlerRun]
  cases result with
  | val values => rfl
  | err error => cases error <;> rfl

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

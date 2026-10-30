import Flapjack.Compiler.Backend.BvlToBvi.Proofs.StateRel
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.StateOk
import Flapjack.Compiler.Backend.Semantics.BvlSem.EvaluateHOL
import Flapjack.Compiler.Backend.Semantics.BviSem.EvaluateList
import Flapjack.Compiler.Backend.Semantics.BviProps.Clock

/-! Cases of the BVL-to-BVI evaluator simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (Result ErrorResult Abort)

/-- The source simulation's result mapping, specialized to relocated BVL
values and BVI exception results. This is Flapjack infrastructure. -/
def mapSimulationResult (relocate : Nat → Nat) : Result (List Value) Value → BviSem.BviResult
  | .val values => .val (values.map (adjustBv relocate))
  | .err (.abort reason) => .err (.abort reason)
  | .err (.raise value) => .err (.raise (.exn (adjustBv relocate value)))

/-- Empty-list case of the source evaluator simulation. It retains the
source theorem's hypotheses and existential result, but is untagged until the
underlying BVI evaluator and the full induction theorem are source-reviewed. -/
theorem compileExpsCorrect_nil {C F : Type} (env : List Value)
    (source next : BvlSem.State (Nat × C) F) (n n2 : Nat)
    (res : Result (List Value) Value) (target : BviSem.BviState C F)
    (ys : List Bvi.Exp) (aux : AppList (Nat × Nat × Bvi.Exp)) (relocate : Nat → Nat)
    (run : BvlSem.evaluate [] env source = (res, next))
    (_notTypeError : res ≠ .err (.abort .typeError))
    (compiled : compileListSource n [] = (ys, aux, n2))
    (related : stateRel relocate source target)
    (_sourceOk : stateOk source) (_envOk : bvOkList source.refs env)
    (_installed : auxCodeInstalled (appListAppend aux) target.code)
    (_handlers : BvlHandle.Proofs.handleOk []) (_global : target.global.isSome = true) :
    ∃ targetNext newRelocate clock,
      BviSem.evaluate ys (env.map (adjustBv newRelocate)) (BviProps.incClock clock target) =
        (mapSimulationResult newRelocate res, targetNext) ∧
      stateRel newRelocate next targetNext ∧
      env.map (adjustBv relocate) = env.map (adjustBv newRelocate) ∧
      ∀ key, source.refs.lookup key ≠ none → relocate key = newRelocate key := by
  simp [BvlSem.evaluate] at run
  rcases run with ⟨rfl, rfl⟩
  simp [compileListSource] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
  · simp [BviSem.evaluate, BviProps.incClock, mapSimulationResult]
  · intro key member
    rfl

/-- Variable case of the source evaluator simulation. An out-of-range
variable is excluded by the original no-type-error premise. This remains
untagged while BVI evaluation and the full induction theorem are reviewed. -/
theorem compileExpsCorrect_var {C F : Type} (index : Nat) (env : List Value)
    (source next : BvlSem.State (Nat × C) F) (n n2 : Nat)
    (res : Result (List Value) Value) (target : BviSem.BviState C F)
    (ys : List Bvi.Exp) (aux : AppList (Nat × Nat × Bvi.Exp)) (relocate : Nat → Nat)
    (run : BvlSem.evaluate [.var index] env source = (res, next))
    (notTypeError : res ≠ .err (.abort .typeError))
    (compiled : compileListSource n [.var index] = (ys, aux, n2))
    (related : stateRel relocate source target)
    (_sourceOk : stateOk source) (_envOk : bvOkList source.refs env)
    (_installed : auxCodeInstalled (appListAppend aux) target.code)
    (_handlers : BvlHandle.Proofs.handleOk [.var index]) (_global : target.global.isSome = true) :
    ∃ targetNext newRelocate clock,
      BviSem.evaluate ys (env.map (adjustBv newRelocate)) (BviProps.incClock clock target) =
        (mapSimulationResult newRelocate res, targetNext) ∧
      stateRel newRelocate next targetNext ∧
      env.map (adjustBv relocate) = env.map (adjustBv newRelocate) ∧
      ∀ key, source.refs.lookup key ≠ none → relocate key = newRelocate key := by
  cases lookup : env[index]? with
  | none =>
    simp [BvlSem.evaluate, lookup] at run
    rcases run with ⟨rfl, _⟩
    exact (notTypeError rfl).elim
  | some value =>
    simp [BvlSem.evaluate, lookup] at run
    rcases run with ⟨rfl, rfl⟩
    simp [compileListSource, compileSingSource, smartAppend] at compiled
    rcases compiled with ⟨rfl, rfl, rfl⟩
    refine ⟨target, relocate, 0, ?_, related, rfl, ?_⟩
    · simp [BviSem.evaluate, BviProps.incClock, mapSimulationResult, lookup]
    · intro key member
      rfl

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

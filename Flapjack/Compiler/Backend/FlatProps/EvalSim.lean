import Flapjack.Compiler.Backend.Semantics.FlatSem.Semantics

/-! Evaluation simulation relation for flat programs. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.SemanticPrimitivesHOL

/-- Simulation of flat declaration evaluation, allowing a target clock
extension and preserving FFI state and result class. The evaluator and
carriers remain pending HOL correspondence review. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "eval_sim_def"]
def evalSim {C₁ C₂ F : Type} (ffi : HolFfiState F) (source target : List FlatLang.Exp)
    (sourceConfig : FlatSem.InstallConfig C₁) (targetConfig : FlatSem.InstallConfig C₂)
    (rel : List FlatLang.Exp → List FlatLang.Exp → Prop) (allowFail : Bool) : Prop :=
  ∀ (clock : Nat) (sourceResult : Option (ErrorResult FlatSem.Value)) (sourceState : FlatSem.State C₁ F),
    FlatSem.evaluateDecs (FlatSem.initialState ffi clock sourceConfig) source = (sourceState, sourceResult) →
    (allowFail = true ∨ sourceResult ≠ some (.abort .typeError)) → rel source target →
    ∃ (extraClock : Nat) (targetResult : Option (ErrorResult FlatSem.Value)) (targetState : FlatSem.State C₂ F),
      FlatSem.evaluateDecs (FlatSem.initialState ffi (clock + extraClock) targetConfig) target = (targetState, targetResult) ∧
      sourceState.ffi = targetState.ffi ∧
      (sourceResult = none → targetResult = none) ∧
      (∀ value, sourceResult = some (.raise value) → ∃ targetValue, targetResult = some (.raise targetValue)) ∧
      (∀ abort, sourceResult = some (.abort abort) → targetResult = some (.abort abort))

end Flapjack.Compiler.Backend.FlatProps

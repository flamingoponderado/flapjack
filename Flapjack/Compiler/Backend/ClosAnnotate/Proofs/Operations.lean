import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Safety
import Flapjack.Compiler.Backend.FlatToClos.Proofs.ErrorPropagation

/-! Ordinary primitive-operation cases of closure annotation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps
open Flapjack.SemanticPrimitivesHOL (Result)

/-- Primitive results relate returned values and states, or relate errors. -/
def AppResultRel {C F : Type} : Result (Value × State C F) Value → Result (Value × State C F) Value → Prop
  | .val (value, state), .val (nextValue, nextState) => ValueRel value nextValue ∧ StateRel state nextState
  | .err error, .err nextError => ResultRel (.err error) (.err nextError)
  | _, _ => False

/-- A primitive simulation obligation, separated from evaluator control flow.
This is Flapjack infrastructure; it does not claim the HOL primitive theorem. -/
def PrimitiveSimulation {C F : Type} (op : ClosLang.Op) : Prop :=
  ∀ (values nextValues : List Value) (source target : State C F),
    List.Forall₂ ValueRel values nextValues → StateRel source target →
    ∃ outcome, doApp op nextValues target = outcome ∧ AppResultRel (doApp op values source) outcome

/-- Evaluation of an ordinary operation after its arguments have returned. -/
theorem evaluate_ordinary_op_values {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (env : List Value) (source middle : State C F) (values : List Value)
    (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsRun : evaluate args env source = (.val values, middle)) :
    evaluate [.op trace op args] env source =
      match doApp op values.reverse middle with
      | .err error => (.err error, middle)
      | .val (value, last) => (.val [value], last) := by
  rw [evaluate, fixClock_evaluate, argsRun]
  cases op with
  | thunkOp thunk =>
    cases thunk <;> simp_all <;> rfl
  | install => exact False.elim (notInstall rfl)
  | label _ | ffi _ | intOp _ | wordOp _ | blockOp _ | globOp _ | memOp _ =>
    rfl

/-- Constructing a block preserves the primitive relation for any related fields. -/
theorem primitiveSimulation_cons {C F : Type} (tag : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.cons tag)) := by
  intro values nextValues source target related states
  exact ⟨.val (.block tag nextValues, target), by simp [doApp, applyBlock], by
    simpa [doApp, applyBlock, AppResultRel] using And.intro (ValueRel.block tag values nextValues related) states⟩

end Flapjack.Compiler.Backend.ClosAnnotate

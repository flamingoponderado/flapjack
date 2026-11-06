import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Safety

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

/-- Evaluation of an ordinary operation when its arguments fail. -/
theorem evaluate_op_error {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (env : List Value) (source middle : State C F)
    (error : Flapjack.SemanticPrimitivesHOL.ErrorResult Value)
    (argsRun : evaluate args env source = (.err error, middle)) :
    evaluate [.op trace op args] env source = (.err error, middle) := by
  rw [evaluate, fixClock_evaluate, argsRun]

/-- Ordinary operation simulation reduces to argument and primitive simulation.
Install and force have separate evaluator control flow. -/
theorem evaluate_ordinary_op {C F : Type} (trace : BackendCommon.Tra) (op : ClosLang.Op)
    (args : List ClosLang.Exp) (notInstall : op ≠ .install) (notForce : op ≠ .thunkOp .forceThunk)
    (argsIH : EvalSimulation (C := C) (F := F) args)
    (primitive : PrimitiveSimulation (C := C) (F := F) op) :
    EvalSimulation (C := C) (F := F) [.op trace op args] := by
  intro env source nextEnv target result sourceNext m l index run noType length vars safe code oracle states
  have argsVars : ∀ n, altFv n args = true → EnvOk m l index env nextEnv n := by
    intro n present
    apply vars n
    simpa [altFv_op] using present
  have argsSafe : everyFnVarsNone args := by simpa [everyFnVarsNone, fnVarsNoneExp] using safe
  cases argsRun : evaluate args env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error =>
      rw [evaluate_op_error trace op args env source middle error argsRun] at run
      cases run
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env source nextEnv target (.err error) sourceNext m l index argsRun noType length argsVars
          argsSafe code oracle states
      cases targetResult with
      | val values => cases error <;> simp [ResultRel] at resultRel
      | err targetError =>
        refine ⟨.err targetError, targetMiddle, ?_, resultRel, middleRel⟩
        rw [altFree_op]
        simp only [shiftList, shiftSing]
        exact evaluate_op_error _ _ _ _ _ _ _ targetRun
    | val values =>
      have valuesNoType : (Result.val values : Result (List Value) Value) ≠ .err (.abort .typeError) := by simp
      obtain ⟨targetResult, targetMiddle, targetRun, resultRel, middleRel⟩ :=
        argsIH env source nextEnv target (.val values) middle m l index argsRun valuesNoType length argsVars
          argsSafe code oracle states
      cases targetResult with
      | err error => cases error <;> simp [ResultRel] at resultRel
      | val targetValues =>
        obtain ⟨outcome, appRun, appRel⟩ := primitive values.reverse targetValues.reverse middle targetMiddle
          (List.forall₂_reverse_iff.mpr resultRel) middleRel
        cases sourceApp : doApp op values.reverse middle with
        | err error =>
          cases outcome with
          | val pair => simp [AppResultRel, sourceApp] at appRel
          | err targetError =>
            rw [evaluate_ordinary_op_values trace op args env source middle values notInstall notForce argsRun, sourceApp] at run
            cases run
            refine ⟨.err targetError, targetMiddle, ?_, ?_, middleRel⟩
            · rw [altFree_op]
              simp only [shiftList, shiftSing]
              rw [evaluate_ordinary_op_values _ _ _ _ _ _ _ notInstall notForce targetRun, appRun]
            · simpa [AppResultRel, sourceApp] using appRel
        | val pair =>
          obtain ⟨value, last⟩ := pair
          cases outcome with
          | err error => simp [AppResultRel, sourceApp] at appRel
          | val targetPair =>
            obtain ⟨targetValue, targetLast⟩ := targetPair
            have related : ValueRel value targetValue ∧ StateRel last targetLast := by
              simpa [AppResultRel, sourceApp] using appRel
            rw [evaluate_ordinary_op_values trace op args env source middle values notInstall notForce argsRun, sourceApp] at run
            cases run
            refine ⟨.val [targetValue], targetLast, ?_, .cons related.1 .nil, related.2⟩
            rw [altFree_op]
            simp only [shiftList, shiftSing]
            rw [evaluate_ordinary_op_values _ _ _ _ _ _ _ notInstall notForce targetRun, appRun]

/-- Constructing a block preserves the primitive relation for any related fields. -/
theorem primitiveSimulation_cons {C F : Type} (tag : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.blockOp (.cons tag)) := by
  intro values nextValues source target related states
  exact ⟨.val (.block tag nextValues, target), by simp [doApp, applyBlock], by
    simpa [doApp, applyBlock, AppResultRel] using And.intro (ValueRel.block tag values nextValues related) states⟩

end Flapjack.Compiler.Backend.ClosAnnotate

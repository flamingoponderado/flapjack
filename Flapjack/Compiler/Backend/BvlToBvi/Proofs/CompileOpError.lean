import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileCall

/-! Argument-failure propagation through BVL-to-BVI operation lowering. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)
open Flapjack.SemanticPrimitivesHOL (ErrorResult)

private theorem op_error {C F : Type} (op : ClosLang.Op) (args : List Bvi.Exp)
    (env : List Value) (state next : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.evaluate args env state = (.err error, next)) :
    BviSem.evaluate [.op op args] env state = (.err error, next) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, run]

private theorem let_error {C F : Type} (args : List Bvi.Exp) (body : Bvi.Exp)
    (env : List Value) (state next : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.evaluate args env state = (.err error, next)) :
    BviSem.evaluate [.let args body] env state = (.err error, next) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, run]

private theorem call_error {C F : Type} (location : Nat) (args : List Bvi.Exp)
    (env : List Value) (state next : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.evaluate args env state = (.err error, next)) :
    BviSem.evaluate [.call 0 (some location) args none] env state = (.err error, next) := by
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, run]
  simp

private theorem append_error {C F : Type} (args suffix : List Bvi.Exp)
    (env : List Value) (state next : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.evaluate args env state = (.err error, next)) :
    BviSem.evaluate (args ++ suffix) env state = (.err error, next) := by
  change BviSem.evaluateTuple (args ++ suffix, env, state) = _
  rw [BviSem.evaluateAppend]
  change BviSem.evaluateTuple (args, env, state) = _ at run
  rw [run]

/-- Lowered operations preserve an operand evaluation failure. This is
Flapjack infrastructure for the operation simulation; it is untagged while
the BVI evaluator is under review. -/
theorem evaluate_compileOp_error {C F : Type} (op : ClosLang.Op) (args : List Bvi.Exp)
    (env : List Value) (state next : BviSem.BviState C F) (error : ErrorResult BviSem.ExnOrRet)
    (run : BviSem.evaluate args env state = (.err error, next)) :
    BviSem.evaluate [compileOp op args] env state = (.err error, next) := by
  cases args with
  | nil => simp [BviSem.evaluate] at run
  | cons first rest =>
    cases op with
    | label name => simpa [compileOp] using op_error _ _ env state next error run
    | ffi name => simpa [compileOp] using op_error _ _ env state next error run
    | wordOp op => simpa [compileOp] using op_error _ _ env state next error run
    | thunkOp op => simpa [compileOp] using op_error _ _ env state next error run
    | intOp op =>
      cases op with
      | const value =>
        have inner := op_error (.intOp (.const 0)) (first :: rest) env state next error run
        have outer := let_error [.op (.intOp (.const 0)) (first :: rest)] (compileInt value) env state next error inner
        simpa [compileOp] using outer
      | _ => simpa [compileOp] using op_error _ _ env state next error run
    | blockOp op =>
      cases op with
      | fromList tag =>
        simp only [compileOp]
        change BviSem.evaluate [.let (first :: rest) _] env state = _
        exact let_error (first :: rest) _ env state next error run
      | _ => simpa [compileOp] using op_error _ _ env state next error run
    | globOp op =>
      cases op with
      | global index => simpa [compileOp] using let_error (first :: rest) _ env state next error run
      | allocGlobal => simpa [compileOp] using call_error allocGlobalLocation (first :: rest) env state next error run
      | _ => simpa [compileOp] using op_error _ _ env state next error run
    | memOp op =>
      cases op with
      | fromListByte | toListByte | concatByteVec =>
        all_goals simp only [compileOp]
        all_goals change BviSem.evaluate [.let (first :: rest) _] env state = _
        all_goals exact let_error (first :: rest) _ env state next error run
      | mutCons | updateCons | finaliseCons =>
        all_goals simpa [compileOp] using let_error (first :: rest) _ env state next error run
      | copyByte flag =>
        cases flag with
        | false => simpa [compileOp] using op_error _ _ env state next error run
        | true =>
          simp only [compileOp]
          split
          · have padded := append_error (first :: rest) (List.replicate 3 (.op (.intOp (.const 0)) []))
              env state next error run
            exact let_error _ _ env state next error padded
          · exact let_error (first :: rest) _ env state next error run
      | _ => simpa [compileOp] using op_error _ _ env state next error run
    | install =>
      simp only [compileOp]
      split
      · have inner := let_error (first :: rest) (.op (.intOp (.const 0)) []) env state next error run
        have listRun : BviSem.evaluate [.let (first :: rest) (.op (.intOp (.const 0)) []),
            .op (.intOp (.const 0)) []] env state = (.err error, next) := by
          change BviSem.evaluateTuple ([.let (first :: rest) (.op (.intOp (.const 0)) []),
            .op (.intOp (.const 0)) []], env, state) = _
          rw [BviSem.evaluateCons]
          change BviSem.evaluateTuple ([.let (first :: rest) (.op (.intOp (.const 0)) [])], env, state) = _ at inner
          rw [inner]
        exact let_error _ _ env state next error listRun
      · exact let_error (first :: rest) _ env state next error run

/-- An operation whose operands fail satisfies the pass simulation whenever
its operand list does. Untagged pending BVI evaluator review. -/
theorem simulation_op_error {C F : Type} (op : ClosLang.Op) (arguments : List Bvl.Exp)
    (env : List Value) (source middle : BvlSem.State (Nat × C) F)
    (error : ErrorResult Value) (argsIH : simulation arguments env source)
    (argsRun : BvlSem.evaluate arguments env source = (.err error, middle)) :
    simulation [.op op arguments] env source := by
  intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
  rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
  have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
  simp [compileListSource, compileSingSource, argsCompile, nilRight] at compiled
  rcases compiled with ⟨rfl, rfl, rfl⟩
  have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
  rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
  simp only at run
  rcases run with ⟨rfl, rfl⟩
  obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
    argsIH n (.err error) middle target finalName argsCode argsAux relocate argsRun notTypeError
      argsCompile related sourceOk envOk installed shape global
  refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
  cases error <;> simp only [mapSimulationResult] at targetArgs ⊢ <;>
    exact evaluate_compileOp_error op argsCode (env.map (adjustBv newRelocate))
      (BviProps.incClock clock target) targetNext _ targetArgs

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

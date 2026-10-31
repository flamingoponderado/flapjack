import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileGlobal

/-! Dynamic global reads in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- The lowered dynamic global-read body selects the corresponding target
slot. Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem evaluate_dynamicGlobalBody {C F : Type} (relocate : Nat → Nat)
    (source : BvlSem.State (Nat × C) F) (target : BviSem.BviState C F)
    (ptr : Nat) (index : Int) (value : Value) (env : List Value)
    (related : stateRel relocate source target) (globalPtr : target.global = some ptr)
    (nonnegative : ¬ index < 0) (slot : source.globals[index.toNat + 1]? = some (some value)) :
    BviSem.evaluate [.op (.memOp .el) [
        .op (.intOp .add) [.op (.intOp (.const 2)) [], .var 0],
        .op (.globOp .globalsPtr) []]] (.number index :: env) target =
      (.val [adjustBv relocate value], target) := by
  obtain ⟨fields, lookup, selected⟩ := stateRel_globalSlot relocate source target ptr (index.toNat + 1) value related globalPtr slot
  have numberIndex : (index + 2).toNat = index.toNat + 2 := by omega
  have nonnegativeIndex : ¬ index + 2 < 0 := by omega
  let constant : Bvi.Exp := .op (.intOp (.const 2)) []
  let varExpr : Bvi.Exp := .var 0
  let add : Bvi.Exp := .op (.intOp .add) [constant, varExpr]
  let global : Bvi.Exp := .op (.globOp .globalsPtr) []
  have constRun : BviSem.evaluate [constant] (.number index :: env) target = (.val [.number 2], target) := by
    simp [constant, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, BackendCommon.smallEnoughInt]
  have varRun : BviSem.evaluate [varExpr] (.number index :: env) target = (.val [.number index], target) := by
    simp [varExpr, BviSem.evaluate]
  have addArgs : BviSem.evaluate [constant, varExpr] (.number index :: env) target =
      (.val [.number 2, .number index], target) := by
    change BviSem.evaluateTuple (constant :: [varExpr], _, _) = _
    rw [BviSem.evaluateCons]
    simp [BviSem.evaluateTuple, constRun, varRun, Flapjack.holHd]
  have addRun : BviSem.evaluate [add] (.number index :: env) target = (.val [.number (index + 2)], target) := by
    dsimp [add]
    rw [BviSem.evaluate, BviSem.fixClock_evaluate, addArgs]
    simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
      BvlSem.applyNumeric, BvlSem.doIntApp, BviSem.fromBvl_toBvl]
  have globalRun : BviSem.evaluate [global] (.number index :: env) target = (.val [.refPtr true ptr], target) := by
    simp [global, BviSem.evaluate, BviSem.fixClock, BviSem.doApp, BviSem.doAppFallback,
      BviSem.doAppAux, globalPtr]
    cases target
    simp_all
  have argsRun : BviSem.evaluate [add, global] (.number index :: env) target =
      (.val [.number (index + 2), .refPtr true ptr], target) := by
    change BviSem.evaluateTuple (add :: [global], _, _) = _
    rw [BviSem.evaluateCons]
    simp [BviSem.evaluateTuple, addRun, globalRun, Flapjack.holHd]
  change BviSem.evaluate [.op (.memOp .el) [add, global]] _ _ = _
  rw [BviSem.evaluate, BviSem.fixClock_evaluate, argsRun]
  simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp,
    BvlSem.applyMemory, BviSem.toBvl, BviSem.fromBvl, lookup, numberIndex,
    nonnegativeIndex, selected]

/-- Global reads satisfy the pass simulation given operand simulation,
including direct and dynamically indexed forms. Untagged pending BVI evaluator
and dispatcher correspondence review. -/
theorem simulation_global {C F : Type} (name : Nat) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.globOp (.global name)) arguments] env source := by
  cases arguments with
  | nil => exact simulation_global_empty name env source
  | cons first rest =>
    cases argsRun : BvlSem.evaluate (first :: rest) env source with
    | mk argsResult middle =>
      cases argsResult with
      | err error => exact simulation_op_error (.globOp (.global name)) (first :: rest) env source middle error argsIH argsRun
      | val values =>
        have valuesLength := BvlSem.evaluate_length (first :: rest) env source middle values argsRun
        intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
        rcases argsCompile : compileListSource n (first :: rest) with ⟨argsCode, argsAux, finalName⟩
        have codeLength := compileListSource_length n (first :: rest)
        rw [argsCompile] at codeLength
        have codeNonempty : argsCode ≠ [] := by intro eq; simp [eq] at codeLength
        have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
        simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp, codeNonempty] at compiled
        rcases compiled with ⟨rfl, rfl, rfl⟩
        have shape : BvlHandle.Proofs.handleOk (first :: rest) := by simpa [BvlHandle.Proofs.handleOk] using handlers
        rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
        cases reversed : values.reverse with
        | nil =>
          have : values = [] := by simpa using congrArg List.reverse reversed
          simp [this] at valuesLength
        | cons input tail =>
          cases tail with
          | cons second tail =>
            cases input <;> cases second <;>
              simp [BvlSem.doApp, BvlSem.applyGlobal, reversed] at run <;>
              exact (notTypeError run.1.symm).elim
          | nil =>
            cases input with
            | number index =>
              by_cases negative : index < 0
              · simp [BvlSem.doApp, BvlSem.applyGlobal, reversed, negative] at run
                exact (notTypeError run.1.symm).elim
              · cases slot : middle.globals[index.toNat + 1]? with
                | none =>
                  simp [BvlSem.doApp, BvlSem.applyGlobal, ClosToBvl.numAddedGlobals, reversed, negative, slot] at run
                  exact (notTypeError run.1.symm).elim
                | some item =>
                  cases item with
                  | none =>
                    simp [BvlSem.doApp, BvlSem.applyGlobal, ClosToBvl.numAddedGlobals, reversed, negative, slot] at run
                    exact (notTypeError run.1.symm).elim
                  | some value =>
                    simp [BvlSem.doApp, BvlSem.applyGlobal, ClosToBvl.numAddedGlobals, reversed, negative, slot] at run
                    rcases run with ⟨rfl, rfl⟩
                    have valuesEq : values = [.number index] := by simpa using congrArg List.reverse reversed
                    obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                      argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                        argsCompile related sourceOk envOk installed shape global
                    have targetGlobal := BviProps.evaluate_global_mono argsCode (env.map (adjustBv newRelocate))
                      (BviProps.incClock clock target) targetNext (.val (values.map (adjustBv newRelocate))) (by
                        simpa [mapSimulationResult] using targetArgs) (by simpa [BviProps.incClock] using global)
                    cases globalPtr : targetNext.global with
                    | none => simp [globalPtr] at targetGlobal
                    | some ptr =>
                      refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
                      rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
                      simp only [mapSimulationResult, valuesEq, List.map_cons, List.map_nil, adjustBv, List.cons_append, List.nil_append]
                      exact evaluate_dynamicGlobalBody newRelocate middle targetNext ptr index value
                        (env.map (adjustBv newRelocate)) relatedNext globalPtr negative slot
            | _ =>
              all_goals
                simp [BvlSem.doApp, BvlSem.applyGlobal, reversed] at run
                exact (notTypeError run.1.symm).elim

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

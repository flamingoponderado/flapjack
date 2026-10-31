import Flapjack.Compiler.Backend.BvlToBvi.Proofs.AllocGlobalRel
import Flapjack.Compiler.Backend.BvlToBvi.Proofs.CompileDynamicGlobal

/-! Global allocation lowering in BVL-to-BVI simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- Global allocation satisfies pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_allocGlobal {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.globOp .allocGlobal) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.globOp .allocGlobal) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases reversed : values.reverse with
      | nil =>
        simp [BvlSem.doApp, BvlSem.applyGlobal, reversed] at run
        exact (notTypeError run.1.symm).elim
      | cons value rest =>
        cases rest with
        | cons second tail =>
          simp [BvlSem.doApp, BvlSem.applyGlobal, reversed] at run
          exact (notTypeError run.1.symm).elim
        | nil =>
          cases value with
          | number integer =>
            cases integer with
            | negSucc count =>
              simp [BvlSem.doApp, BvlSem.applyGlobal, reversed] at run
              exact (notTypeError run.1.symm).elim
            | ofNat count =>
              simp [BvlSem.doApp, BvlSem.applyGlobal, reversed] at run
              rcases run with ⟨rfl, rfl⟩
              have valuesEq : values = [.number (Int.ofNat count)] := by simpa using congrArg List.reverse reversed
              obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
                argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
                  argsCompile related sourceOk envOk installed shape global
              have targetGlobal := BviProps.evaluate_global_mono argsCode (env.map (adjustBv newRelocate))
                (BviProps.incClock clock target) targetNext (.val (values.map (adjustBv newRelocate))) (by
                  simpa [mapSimulationResult] using targetArgs) (by simpa [BviProps.incClock] using global)
              cases globalPtr : targetNext.global with
              | none => simp [globalPtr] at targetGlobal
              | some ptr =>
                obtain ⟨_, size, arrayLookup, sizeBound⟩ := relatedNext.2.2.1 ptr globalPtr
                let fields := middle.globals.map (fun value => (value.map (adjustBv newRelocate)).getD (.number 0)) ++
                  List.replicate (size - (middle.globals.length + 1)) (.number 0)
                have lookup : targetNext.refs.lookup ptr = some (.valueArray (.number (Int.ofNat (middle.globals.length + 1)) :: fields)) := arrayLookup
                have bound : middle.globals.length ≤ fields.length := by simp [fields]
                have copyCode : sptLookup copyGlobalsLocation targetNext.code = some copyGlobalsCode := relatedNext.2.2.2.2.2.2.2.1
                obtain ⟨newPtr, stubClock, extra, fresh, capacity, stubRun⟩ :=
                  evaluate_allocGlobal ptr middle.globals.length count fields targetNext globalPtr lookup bound copyCode
                have relFinal := stateRel_allocGlobal newRelocate middle targetNext ptr newPtr count extra fields relatedNext globalPtr lookup fresh capacity
                let added := stubClock + 1
                have shifted := BviProps.evaluate_inv_clock argsCode (env.map (adjustBv newRelocate))
                  (BviProps.incClock clock target) targetNext (.val (values.map (adjustBv newRelocate))) added
                  (by simpa [mapSimulationResult] using targetArgs) (by simp)
                rw [BviProps.incClock_add] at shifted
                refine ⟨{ targetNext with
                    global := some newPtr
                    refs := (targetNext.refs.updateEq (ptr, .valueArray (.number (Int.ofNat (middle.globals.length + count + 1)) :: fields))).updateEq
                      (newPtr, .valueArray (.number (Int.ofNat (middle.globals.length + count + 1)) :: fields ++ List.replicate extra (.number 0))) },
                  newRelocate, added + clock, ?_, relFinal, envEq, refsEq⟩
                rw [BviSem.evaluate, BviSem.fixClock_evaluate, shifted]
                simp only [mapSimulationResult, valuesEq, List.map_cons, List.map_nil, adjustBv]
                have startCode : sptLookup allocGlobalLocation (BviProps.incClock added targetNext).code = some allocGlobalCode := by
                  simpa [BviProps.incClock] using relatedNext.2.2.2.2.2.2.1
                have nonzero : (BviProps.incClock added targetNext).clock ≠ 0 := by simp [BviProps.incClock, added]
                have clocks : BviSem.decClock 1 (BviProps.incClock added targetNext) = BviProps.incClock stubClock targetNext := by
                  simp [BviSem.decClock, BviProps.incClock, added]
                simp only [BvlSem.findCode, startCode, allocGlobalCode, List.length_cons, List.length_nil, ite_true,
                  Nat.zero_add, Nat.lt_one_iff, nonzero, if_false, BviSem.fixClock_evaluate]
                simp [allocGlobalCode] at stubRun
                simp [clocks, stubRun, adjustBv, adjustValues, BvlSem.unitValue]
          | _ =>
            all_goals
              simp [BvlSem.doApp, BvlSem.applyGlobal, reversed] at run
              exact (notTypeError run.1.symm).elim

/-- Every global operation satisfies pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_globOp {C F : Type} (op : ClosLang.GlobOp) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.globOp op) arguments] env source := by
  cases op with
  | global index => exact simulation_global index arguments env source argsIH
  | setGlobal index => exact simulation_setGlobal index arguments env source argsIH
  | allocGlobal => exact simulation_allocGlobal arguments env source argsIH
  | globalsPtr => exact simulation_globalPointerUnsupported _ arguments env source (by simp) argsIH
  | setGlobalsPtr => exact simulation_globalPointerUnsupported _ arguments env source (by simp) argsIH

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

import Flapjack.Compiler.Backend.BvlToBvi.Proofs.BuildSimulation

/-! Source type-error cases in BVL-to-BVI operation simulation. -/
namespace Flapjack.Compiler.Backend.BvlToBvi.Proofs
open Flapjack.Compiler.Backend.BvlSem (Value)

/-- An operation that always yields the source type error satisfies the pass
simulation when operand evaluation is simulated. Operand failures still
propagate through the generated lowering. -/
theorem simulation_alwaysTypeError {C F : Type} (op : ClosLang.Op) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source)
    (alwaysError : ∀ (args : List Value) (state : BvlSem.State (Nat × C) F),
      BvlSem.doApp op args state = .err (.abort .typeError)) :
    simulation [.op op arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error op arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      simp [alwaysError] at run
      exact (notTypeError run.1.symm).elim

/-- Operations reserved for later languages have no successful BVL application.
Their operand errors are handled by the generic failure simulation. -/
theorem simulation_sourceUnsupported {C F : Type} (op : ClosLang.MemOp) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (unsupported : op = .refByte true ∨ op = .lengthByteVec ∨ op = .derefByteVec ∨
      (∃ tag index, op = .mutCons tag index) ∨ op = .updateCons ∨ op = .finaliseCons)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp op) arguments] env source := by
  apply simulation_alwaysTypeError _ arguments env source argsIH
  intro args state
  rcases unsupported with h | h | h | ⟨tag, index, h⟩ | h | h <;> subst op <;>
    simp [BvlSem.doApp, BvlSem.applyMemory]

/-- The source-only global-pointer operations always fail at BVL level. -/
theorem simulation_globalPointerUnsupported {C F : Type} (op : ClosLang.GlobOp) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (unsupported : op = .globalsPtr ∨ op = .setGlobalsPtr)
    (argsIH : simulation arguments env source) :
    simulation [.op (.globOp op) arguments] env source := by
  apply simulation_alwaysTypeError _ arguments env source argsIH
  intro args state
  rcases unsupported with h | h <;> subst op <;> simp [BvlSem.doApp, BvlSem.applyGlobal]

/-- The source constant-constructor operation always fails at BVL level. -/
theorem simulation_constantUnsupported {C F : Type} (constant : ClosLang.Const) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp (.constant constant)) arguments] env source := by
  apply simulation_alwaysTypeError _ arguments env source argsIH
  intro args state
  simp [BvlSem.doApp, BvlSem.applyBlock]

/-- Successful GC configuration has two integer operands and changes no state. -/
theorem configGC_shape {C F : Type} (args : List Value) (source next : BvlSem.State C F) (value : Value)
    (run : BvlSem.applyMemory .configGC args source = some (value, next)) :
    ∃ left right, args = [.number left, .number right] ∧ value = BvlSem.unitValue ∧ next = source := by
  unfold BvlSem.applyMemory at run
  repeat' first | split at run | contradiction
  all_goals simp_all

/-- GC configuration satisfies pass simulation given operand simulation.
Untagged pending BVI evaluator and dispatcher correspondence review. -/
theorem simulation_configGC {C F : Type} (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.memOp .configGC) arguments] env source := by
  cases argsRun : BvlSem.evaluate arguments env source with
  | mk argsResult middle =>
    cases argsResult with
    | err error => exact simulation_op_error (.memOp .configGC) arguments env source middle error argsIH argsRun
    | val values =>
      intro n res next target n2 ys aux relocate run notTypeError compiled related sourceOk envOk installed handlers global
      rcases argsCompile : compileListSource n arguments with ⟨argsCode, argsAux, finalName⟩
      have nilRight : smartAppend argsAux .nil = argsAux := by cases argsAux <;> rfl
      simp [compileListSource, compileSingSource, argsCompile, nilRight, compileOp] at compiled
      rcases compiled with ⟨rfl, rfl, rfl⟩
      have shape : BvlHandle.Proofs.handleOk arguments := by simpa [BvlHandle.Proofs.handleOk] using handlers
      rw [BvlSem.evaluate, BvlSem.fixClock_evaluate, argsRun] at run
      cases application : BvlSem.applyMemory .configGC values.reverse middle with
      | none =>
        simp [BvlSem.doApp, application] at run
        exact (notTypeError run.1.symm).elim
      | some pair =>
        rcases pair with ⟨result, last⟩
        obtain ⟨left, right, argsEq, resultEq, lastEq⟩ := configGC_shape values.reverse middle last result application
        subst result
        subst last
        simp [BvlSem.doApp, application] at run
        rcases run with ⟨rfl, rfl⟩
        obtain ⟨targetNext, newRelocate, clock, targetArgs, relatedNext, envEq, refsEq⟩ :=
          argsIH n (.val values) middle target finalName argsCode argsAux relocate argsRun (by simp)
            argsCompile related sourceOk envOk installed shape global
        refine ⟨targetNext, newRelocate, clock, ?_, relatedNext, envEq, refsEq⟩
        rw [BviSem.evaluate, BviSem.fixClock_evaluate, targetArgs]
        simp only [mapSimulationResult]
        rw [← List.map_reverse, argsEq]
        simp [BviSem.doApp, BviSem.doAppFallback, BviSem.doAppAux, BvlSem.doApp, BvlSem.applyMemory,
          BviSem.fromBvl_toBvl, adjustBv, BvlSem.unitValue, adjustValues]

/-- Every block operation satisfies the pass simulation given its operand
simulation. Untagged pending BVI evaluator and dispatcher review. -/
theorem simulation_blockOp {C F : Type} (op : ClosLang.BlockOp) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.blockOp op) arguments] env source := by
  cases op with
  | cons tag => exact simulation_blockCons tag arguments env source argsIH
  | elemAt index => exact simulation_elemAt index arguments env source argsIH
  | tagLenEq tag length =>
    simpa [BlockObservation.op] using simulation_blockObservation (.tagLenEq tag length) arguments env source argsIH
  | lenEq length =>
    simpa [BlockObservation.op] using simulation_blockObservation (.lenEq length) arguments env source argsIH
  | tagEq tag =>
    simpa [BlockObservation.op] using simulation_blockObservation (.tagEq tag) arguments env source argsIH
  | lengthBlock =>
    simpa [BlockObservation.op] using simulation_blockObservation .length arguments env source argsIH
  | boolTest test => exact simulation_boolTest test arguments env source argsIH
  | boolNot => exact simulation_boolNot arguments env source argsIH
  | boundsCheckBlock => exact simulation_blockBounds arguments env source argsIH
  | consExtend tag => exact simulation_consExtend tag arguments env source argsIH
  | fromList tag => exact simulation_fromList tag arguments env source argsIH
  | listAppend => exact simulation_listAppend arguments env source argsIH
  | constant constant => exact simulation_constantUnsupported constant arguments env source argsIH
  | equal => exact simulation_equal arguments env source argsIH
  | equalConst part => exact simulation_equalConst part arguments env source argsIH
  | build parts => exact simulation_build parts arguments env source argsIH

/-- Every thunk operation satisfies pass simulation given operand simulation. -/
theorem simulation_thunkOp {C F : Type} (op : AstHOL.ThunkOp) (arguments : List Bvl.Exp)
    (env : List Value) (source : BvlSem.State (Nat × C) F)
    (argsIH : simulation arguments env source) :
    simulation [.op (.thunkOp op) arguments] env source := by
  cases op with
  | allocThunk mode => exact simulation_allocThunk mode arguments env source argsIH
  | updateThunk mode => exact simulation_updateThunk mode arguments env source argsIH
  | forceThunk =>
    apply simulation_alwaysTypeError _ arguments env source argsIH
    intro args state
    simp [BvlSem.doApp]

end Flapjack.Compiler.Backend.BvlToBvi.Proofs

import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshTargetRefs
import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence

/-! Scalar and empty-block constants for closure-to-BVL. -/
namespace Flapjack.Compiler.Backend.ClosToBvl
open Flapjack.SemanticPrimitivesHOL Flapjack.SemanticPrimitivesProps Flapjack.Compiler.Backend.BackendCommon
open Flapjack.Basis.Pure.MlString

/-- Constants built by at most one primitive target allocation. -/
inductive ScalarConstant where
  | int : Int → ScalarConstant
  | word : BitVec 64 → ScalarConstant
  | string : MlString → ScalarConstant
  | emptyBlock : Nat → ScalarConstant

/-- The source constant corresponding to a scalar case. -/
def ScalarConstant.constant : ScalarConstant → ClosLang.Const
  | .int n => .constInt n
  | .word w => .constWord64 w
  | .string text => .constStr text
  | .emptyBlock tag => .constCons tag []

/-- Scalar constants produce related values while preserving the state
relation and the frame of previously unmapped references. -/
theorem scalarConstant_dispatch {C F : Type} (constant : ScalarConstant)
    (s : ClosSem.State C F) (t : BvlSem.State C F) (f : HolFiniteMapExact Nat Nat)
    (states : stateRel f s t) :
    ∃ target next,
      ClosSem.doApp (.blockOp (.constant constant.constant)) [] s =
        .val (ClosSem.makeConst constant.constant, s) ∧
      BvlSem.doApp (compileConst constant.constant) [] t = .val (target, next) ∧
      vRel s.maxApp f next.refs next.code (ClosSem.makeConst constant.constant) target ∧
      stateRel f s next ∧ unmappedRefsSubmap t.refs next.refs f f ∧ next.clock = t.clock := by
  have frame : unmappedRefsSubmap t.refs t.refs f f := by
    intro key value found fresh
    exact ⟨found, fresh⟩
  cases constant with
  | int n =>
    simp only [ScalarConstant.constant, ClosSem.makeConst]
    refine ⟨.number n, t, by simp [ClosSem.doApp, ClosSem.applyBlock, ClosSem.makeConst], ?_, .number n, states, frame, rfl⟩
    simp [compileConst, BvlSem.doApp, BvlSem.applyNumeric, BvlSem.doIntApp]
  | word w =>
    simp only [ScalarConstant.constant, ClosSem.makeConst]
    refine ⟨.word64 w, t, by simp [ClosSem.doApp, ClosSem.applyBlock, ClosSem.makeConst], ?_, .word64 w, states, frame, rfl⟩
    simp [compileConst, BvlSem.doApp, BvlSem.applyBlock,
      BvlSem.doBuildConst, BvlSem.doBuild, BvlSem.doPart]
  | emptyBlock tag =>
    simp only [ScalarConstant.constant, ClosSem.makeConst]
    refine ⟨.block (closTagShift tag) [], t, by simp [ClosSem.doApp, ClosSem.applyBlock, ClosSem.makeConst], ?_, .block .nil, states, frame, rfl⟩
    simp [compileConst, BvlSem.doApp, BvlSem.applyBlock]
  | string text =>
    simp only [ScalarConstant.constant, ClosSem.makeConst]
    let ptr := BvlSem.leastUnusedRef t.refs
    let next := { t with refs := t.refs.updateEq (ptr, .byteArray true text.explode) }
    have fresh := stateRel_targetRefs_allocate s t f (.byteArray true text.explode) states
    change stateRel f s next ∧ unmappedRefsSubmap t.refs next.refs f f ∧
      (¬ ∃ sourcePtr, f.lookup sourcePtr = some ptr) ∧
      next.refs.lookup ptr = some (.byteArray true text.explode) at fresh
    refine ⟨.refPtr true ptr, next, by simp [ClosSem.doApp, ClosSem.applyBlock, ClosSem.makeConst], ?_, .byteVector fresh.2.2.2 fresh.2.2.1, fresh.1, fresh.2.1, rfl⟩
    simp [compileConst, BvlSem.doApp, BvlSem.applyBlock,
      BvlSem.doBuildConst, BvlSem.doBuild, BvlSem.doPart, ptr, next]

/-- The scalar-constant expression case, including target-only allocation of
frozen string bytes. This candidate remains untagged pending semantic-carrier
review and assembly of the full pass theorem. -/
theorem expressionSimulation_scalarConstant {C F : Type} (trace : BackendCommon.Tra)
    (constant : ScalarConstant) : expressionSimulation (C := C) (F := F)
      [.op trace (.blockOp (.constant constant.constant)) []] := by
  intro s sFinal t sourceEnv targetEnv f aux finalAux compiled result run noTypeError compile
    locations annotations varsAnnotated installed envRelated states
  have sourceRun : ClosSem.evaluate [.op trace (.blockOp (.constant constant.constant)) []] sourceEnv s =
      (.val [ClosSem.makeConst constant.constant], s) := by
    rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
    simp [ClosSem.evaluate, ClosSem.doApp, ClosSem.applyBlock]
  have resultEq := run.symm.trans sourceRun
  cases resultEq
  have compilerRun : compileExpsHOL s.maxApp [.op trace (.blockOp (.constant constant.constant)) []] aux =
      ([.op (compileConst constant.constant) []], aux) := by
    rw [compileExps_eq_list]
    simp [compileExpListHOL, compileExpHOL, compileOp]
  have compilerEq := compile.symm.trans compilerRun
  cases compilerEq
  let start : BvlSem.State C F := { t with clock := s.clock }
  have startRel : stateRel f s start := (stateRel_clock f s t s.clock).1.mpr states
  obtain ⟨target, next, _, targetApp, valueRel, nextRel, frame, clock⟩ :=
    scalarConstant_dispatch constant s start f startRel
  refine ⟨0, .val [target], next, f, ?_, ?_, nextRel, ?_, ?_, annotations, ?_⟩
  · rw [BvlSem.evaluate, BvlSem.fixClock_evaluate]
    simp [BvlSem.evaluate, targetApp, start]
  · exact List.Forall₂.cons valueRel .nil
  · intro key value lookup
    exact lookup
  · exact frame
  · simpa [start] using clock.symm

end Flapjack.Compiler.Backend.ClosToBvl

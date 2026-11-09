module

public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.FreshTargetRefs
public import Flapjack.Compiler.Backend.ClosToBvl.Proofs.EvaluateSequence

@[expose] public section

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

end Flapjack.Compiler.Backend.ClosToBvl

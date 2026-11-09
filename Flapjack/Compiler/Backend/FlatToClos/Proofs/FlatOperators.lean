import Flapjack.Compiler.Backend.FlatToClos.Proofs.SpecialOperators
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Globals
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Element

/-! Flat-specific operator simulations. These use proof-side semantic
relations and are not reviewed HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Every Flat-specific operator is simulated for arbitrary arguments.
The source-operator case is handled separately by `evaluate_sourceOp`. -/
theorem evaluate_flatOp {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (notSource : ∀ sourceOp, op ≠ .src sourceOp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace op args]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace op args] := by
  have globalSim (category : (∃ n, op = .globalVarLookup n) ∨
      (∃ n, op = .globalVarInit n) ∨ (∃ n, op = .globalVarAlloc n)) :
      EvalSim env names values source target [.app trace op args] := by
    have facts : destNop op args = none ∧ op ≠ .src .opapp ∧ op ≠ .src .eval ∧
        op ≠ .src (.thunkOp .forceThunk) := by
      rcases category with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp [destNop]
    apply evalSim_app_of_op env names values source target trace op args
      facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 ?_ argsSim notTypeError
    intro s vs sNext result tNext xs db t ws tt premises
    exact opGlobals op s vs sNext result tNext xs db t ws tt category premises
  have blockSim (category : (∃ tag n, op = .tagLenEq tag n) ∨
      (∃ n, op = .lenEq n) ∨ op = .src .listAppend) :
      EvalSim env names values source target [.app trace op args] := by
    have facts : destNop op args = none ∧ op ≠ .src .opapp ∧ op ≠ .src .eval ∧
        op ≠ .src (.thunkOp .forceThunk) := by
      rcases category with ⟨_, _, rfl⟩ | ⟨_, rfl⟩ | rfl <;> simp [destNop]
    apply evalSim_app_of_op env names values source target trace op args
      facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 ?_ argsSim notTypeError
    intro s vs sNext result tNext xs db t ws tt premises
    exact opBlocks op s vs sNext result tNext xs db t ws tt category premises
  have refSim (category : op = .src .opref ∨ (∃ n, op = .el n) ∨
      op = .src .opassign) : EvalSim env names values source target [.app trace op args] := by
    have facts : destNop op args = none ∧ op ≠ .src .opapp ∧ op ≠ .src .eval ∧
        op ≠ .src (.thunkOp .forceThunk) := by
      rcases category with rfl | ⟨_, rfl⟩ | rfl <;> simp [destNop]
    apply evalSim_app_of_op env names values source target trace op args
      facts.1 facts.2.1 facts.2.2.1 facts.2.2.2 ?_ argsSim notTypeError
    intro s vs sNext result tNext xs db t ws tt premises
    exact opRefs op s vs sNext result tNext xs db t ws tt category premises
  cases op with
  | src sourceOp => exact (notSource sourceOp rfl).elim
  | globalVarAlloc count => exact globalSim (Or.inr (Or.inr ⟨count, rfl⟩))
  | globalVarInit index => exact globalSim (Or.inr (Or.inl ⟨index, rfl⟩))
  | globalVarLookup index => exact globalSim (Or.inl ⟨index, rfl⟩)
  | tagLenEq tag length => exact blockSim (Or.inl ⟨tag, length, rfl⟩)
  | lenEq length => exact blockSim (Or.inr (Or.inl ⟨length, rfl⟩))
  | el index => exact refSim (Or.inr (Or.inl ⟨index, rfl⟩))
  | id =>
    apply evalSim_app_of_op env names values source target trace .id args
      ?_ (by simp) (by simp) (by simp) ?_ argsSim notTypeError
    · simp [destNop]
    · intro s vs sNext result tNext xs db t ws tt premises
      exact opId _ s vs sNext result tNext xs db t ws tt rfl premises



/-- All Flat operators simulate under the stated expression and declaration
induction hypotheses. The synthetic thunk-body and installation premises
remain to be discharged, and these proof-side relations await HOL review. -/
theorem evaluate_operator {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp)
    (states : StateRel source target)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (operandSim : ∀ (expression : FlatLang.Exp) (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      expression ∈ args → StateRel next nextTarget → next.clock ≤ source.clock →
      (FlatSem.evaluate env next [expression]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values next nextTarget [expression])
    (charInnerSim : ∀ innerTrace inner,
      args = [.app innerTrace (.src (.fromTo .charT .intT)) [inner]] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (wordInnerSim : ∀ innerTrace inner,
      args = [.app innerTrace (.src (.fromTo (.wordT .w8) .intT)) [inner]] →
      (FlatSem.evaluate env source [inner]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target [inner])
    (bodySim : ∀ (next : FlatSem.State C F) (nextTarget : ClosSem.State C F)
        (nextEnv : FlatSem.Environment FlatSem.Value) (body : FlatLang.Exp)
        (newNames : List (Option MlString)) (newValues : List ClosSem.Value),
      next.clock ≤ source.clock → next.clock ≠ 0 → EnvRel nextEnv newNames newValues → FlatProps.noMat body = true →
      StateRel (FlatSem.decClock next) (ClosSem.decClock 1 nextTarget) →
      (FlatSem.evaluate nextEnv (FlatSem.decClock next) [body]).2 ≠ .err (.abort .typeError) →
      EvalSim nextEnv newNames newValues (FlatSem.decClock next) (ClosSem.decClock 1 nextTarget) [body])
    (forceSim : ∀ (sourceValue : FlatSem.Value) (targetValue : ClosSem.Value)
        (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      op = .src (.thunkOp .forceThunk) → ValueRel sourceValue targetValue → StateRel next nextTarget → next.clock ≤ source.clock →
      (FlatSem.evaluate ⟨[(ofString "f", sourceValue)]⟩ next
        [FlatSem.appUnit (.varLocal .none (ofString "f"))]).2 ≠ .err (.abort .typeError) →
      EvalSim ⟨[(ofString "f", sourceValue)]⟩ [some (ofString "f")] [targetValue] next nextTarget
        [FlatSem.appUnit (.varLocal .none (ofString "f"))])
    (decsSim : ∀ (decs : List FlatLang.Exp) (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      StateRel next nextTarget → next.clock < source.clock → FlatProps.noMatDecs decs = true →
      (FlatSem.evaluateDecs next decs).2 ≠ some (.abort .typeError) → DecUnitSim next nextTarget decs)
    (notTypeError : (FlatSem.evaluate env source [.app trace op args]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace op args] := by
  cases op with
  | src op =>
    exact evaluate_sourceOp env names values source target trace op args states argsSim
      operandSim charInnerSim wordInnerSim bodySim
      (fun sv tv next nextTarget equal => forceSim sv tv next nextTarget (by cases equal; rfl))
      decsSim notTypeError
  | globalVarAlloc count => exact evaluate_flatOp env names values source target trace _ args (by simp) argsSim notTypeError
  | globalVarInit index => exact evaluate_flatOp env names values source target trace _ args (by simp) argsSim notTypeError
  | globalVarLookup index => exact evaluate_flatOp env names values source target trace _ args (by simp) argsSim notTypeError
  | tagLenEq tag length => exact evaluate_flatOp env names values source target trace _ args (by simp) argsSim notTypeError
  | lenEq length => exact evaluate_flatOp env names values source target trace _ args (by simp) argsSim notTypeError
  | el index => exact evaluate_flatOp env names values source target trace _ args (by simp) argsSim notTypeError
  | id => exact evaluate_flatOp env names values source target trace _ args (by simp) argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos

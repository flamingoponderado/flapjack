module

public import Flapjack.Compiler.Backend.FlatToClos.Proofs.SpecialOperators
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Globals
public import Flapjack.Compiler.Backend.FlatToClos.Proofs.Element

@[expose] public section

/-! Flat-specific operator simulations. These use proof-side semantic
relations and are not reviewed HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

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
  have flatSim (noNop : destNop op args = none) (notApp : op ≠ .src .opapp)
      (notEval : op ≠ .src .eval) (notForce : op ≠ .src (.thunkOp .forceThunk)) :
      EvalSim env names values source target [.app trace op args] := by
    apply evalSim_app_of_op env names values source target trace op args
      noNop notApp notEval notForce ?_ argsSim notTypeError
    intro s vs sNext result tNext xs db t ws tt premises
    exact compileOpCorrect s op vs sNext result tNext xs db t ws tt premises
  cases op with
  | src op =>
    exact evaluate_sourceOp env names values source target trace op args states argsSim
      operandSim charInnerSim wordInnerSim bodySim
      (fun sv tv next nextTarget equal => forceSim sv tv next nextTarget (by cases equal; rfl))
      decsSim notTypeError
  | globalVarAlloc _ | globalVarInit _ | globalVarLookup _ | tagLenEq _ _ | lenEq _ | el _ | id =>
    apply flatSim <;> simp [destNop]

end Flapjack.Compiler.Backend.FlatToClos

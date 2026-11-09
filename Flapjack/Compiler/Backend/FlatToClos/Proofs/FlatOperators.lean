import Flapjack.Compiler.Backend.FlatToClos.Proofs.SpecialOperators
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Globals
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Element

/-! Flat-specific operator simulations. These use proof-side semantic
relations and are not reviewed HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Expected arity of each Flat-specific operator. -/
def flatOpArity : FlatLang.Op → Option Nat
  | .globalVarAlloc _ | .globalVarLookup _ => some 0
  | .globalVarInit _ | .tagLenEq _ _ | .lenEq _ | .el _ | .id => some 1
  | .src _ => none

/-- Flat-specific operators reject wrong value counts. -/
theorem flatOp_wrong_arity {C F : Type} (state : FlatSem.State C F)
    (op : FlatLang.Op) (args : List FlatSem.Value) (arity : Nat)
    (expected : flatOpArity op = some arity) (wrong : args.length ≠ arity) :
    (FlatSem.applyResult state op args).2 = .err (.abort .typeError) := by
  cases op <;> simp [flatOpArity] at expected
  all_goals subst arity
  all_goals rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩
  all_goals simp_all [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat]

/-- The remaining Flat operators lower wrong-arity applications to a closure
let that evaluates the same arguments before its body. -/
inductive FlatLetOp : FlatLang.Op → Prop where
  | el (index : Nat) : FlatLetOp (.el index)

theorem flatLetOp_compile_wrong (names : List (Option MlString)) (trace : BackendCommon.Tra)
    (op : FlatLang.Op) (args : List FlatLang.Exp) (arity : Nat) (kind : FlatLetOp op)
    (expected : flatOpArity op = some arity) (wrong : args.length ≠ arity) :
    ∃ t body, compileExp names (.app trace op args) =
      .let t (compileExps names args).reverse body := by
  cases kind with
  | el index =>
    simp [flatOpArity] at expected
    subst arity
    rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp_all [compileExp, destNop, compileOp, compileExps, arg1]
    all_goals
      split
      · rename_i h
        have lengths := congrArg List.length h
        simp at lengths
      · exact ⟨.none, _, rfl⟩
/-- Wrong-arity let-lowered Flat operations preserve argument errors; a successful
argument list would force a source type error. -/
theorem evaluate_flatLet_wrong {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op)
    (args : List FlatLang.Exp) (arity : Nat) (kind : FlatLetOp op)
    (expected : flatOpArity op = some arity) (wrong : args.length ≠ arity)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace op args]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace op args] := by
  have flatFix := (FlatSem.fixClock_evaluations env source args.reverse (.lit .none (.intLit 0)) []).1
  have closFix := ClosSem.fixClock_evaluate (compileExps names args).reverse values target
  have argsNotTypeError : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) := by
    intro failure
    apply notTypeError
    rw [FlatSem.evaluate]
    simp only [flatFix, failure]
  have argsSim := argsSim argsNotTypeError
  unfold EvalSim at argsSim ⊢
  simp only [compile, compileExps_reverse] at argsSim
  simp only [compile, compileExps] at ⊢
  obtain ⟨closTrace, body, compiled⟩ := flatLetOp_compile_wrong names trace op args arity kind expected wrong
  rw [compiled, FlatSem.evaluate, ClosSem.evaluate, closFix]
  simp only [flatFix]
  cases flatRun : FlatSem.evaluate env source args.reverse with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate (compileExps names args).reverse values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argsSim ⊢
      rcases argsSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        rename_i sourceArgs targetArgs
        have resultLength := FlatSem.evaluate_length env source next args.reverse sourceArgs flatRun
        simp only [List.length_reverse] at resultLength
        have sourceWrong : sourceArgs.reverse.length ≠ arity := by simpa [resultLength] using wrong
        have failure := flatOp_wrong_arity next op sourceArgs.reverse arity expected sourceWrong
        have fixed := flatFix
        rw [flatRun] at fixed
        apply False.elim
        apply notTypeError
        rw [FlatSem.evaluate, flatRun, fixed]
        cases kind
        simpa using failure


/-- Every Flat-specific operator is simulated for arbitrary arguments.
The source-operator case is handled separately by `evaluate_sourceOp`. -/
theorem evaluate_flatOp {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : FlatLang.Op) (args : List FlatLang.Exp) (arity : Nat)
    (expected : flatOpArity op = some arity)
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
  by_cases wrong : args.length ≠ arity
  · cases op with
    | src _ => simp [flatOpArity] at expected
    | globalVarAlloc count => exact globalSim (Or.inr (Or.inr ⟨count, rfl⟩))
    | globalVarInit index => exact globalSim (Or.inr (Or.inl ⟨index, rfl⟩))
    | globalVarLookup index => exact globalSim (Or.inl ⟨index, rfl⟩)
    | tagLenEq tag length => exact blockSim (Or.inl ⟨tag, length, rfl⟩)
    | lenEq length => exact blockSim (Or.inr (Or.inl ⟨length, rfl⟩))
    | el index => exact evaluate_flatLet_wrong env names values source target trace _ args arity (.el index) expected wrong argsSim notTypeError
    | id =>
      apply evalSim_app_of_op env names values source target trace .id args
        ?_ (by simp) (by simp) (by simp) ?_ argsSim notTypeError
      · simp [destNop]
      · intro s vs sNext result tNext xs db t ws tt premises
        exact opId _ s vs sNext result tNext xs db t ws tt rfl premises
  · have right : args.length = arity := by omega
    cases op with
    | src _ => simp [flatOpArity] at expected
    | globalVarAlloc index => exact globalSim (Or.inr (Or.inr ⟨index, rfl⟩))
    | globalVarLookup index => exact globalSim (Or.inl ⟨index, rfl⟩)
    | globalVarInit index => exact globalSim (Or.inr (Or.inl ⟨index, rfl⟩))
    | tagLenEq tag length => exact blockSim (Or.inl ⟨tag, length, rfl⟩)
    | lenEq length => exact blockSim (Or.inr (Or.inl ⟨length, rfl⟩))
    | el index =>
      simp [flatOpArity] at expected
      subst arity
      cases args with
      | nil => simp at expected
      | cons argument rest =>
        cases rest with
        | cons extra rest => simp at expected
        | nil =>
          exact evaluate_element env names values source target trace index argument (by simpa using argsSim) notTypeError
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
  | globalVarAlloc count => exact evaluate_flatOp env names values source target trace _ args 0 rfl argsSim notTypeError
  | globalVarInit index => exact evaluate_flatOp env names values source target trace _ args 1 rfl argsSim notTypeError
  | globalVarLookup index => exact evaluate_flatOp env names values source target trace _ args 0 rfl argsSim notTypeError
  | tagLenEq tag length => exact evaluate_flatOp env names values source target trace _ args 1 rfl argsSim notTypeError
  | lenEq length => exact evaluate_flatOp env names values source target trace _ args 1 rfl argsSim notTypeError
  | el index => exact evaluate_flatOp env names values source target trace _ args 1 rfl argsSim notTypeError
  | id => exact evaluate_flatOp env names values source target trace _ args 1 rfl argsSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos

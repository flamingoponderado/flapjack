import Flapjack.Compiler.Backend.FlatToClos.Proofs.SourceOperators
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Application
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Assignment
import Flapjack.Compiler.Backend.FlatToClos.Proofs.Force
import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvalInstall

/-! Special operator cases for the proof-side evaluator simulation. These
lemmas are infrastructure and have not been reviewed as HOL theorem ports. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.AstHOL Flapjack.Basis.Pure.MlString

/-- Neither application nor assignment accepts a non-binary argument list. -/
theorem binarySpecial_rejects {C F : Type} (state : FlatSem.State C F)
    (op : AstHOL.Op) (args : List FlatSem.Value)
    (special : op = .opapp ∨ op = .opassign) (wrong : args.length ≠ 2) :
    (op = .opapp → FlatSem.doOpApp args = none) ∧
    (op = .opassign → (FlatSem.applyResult state (.src op) args).2 = .err (.abort .typeError)) := by
  rcases special with rfl | rfl
  · rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;> simp_all [FlatSem.doOpApp]
  · rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
      simp_all [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, FlatSem.doAppMemory]

/-- The wrong-arity lowering still evaluates arguments in the original order. -/
theorem binarySpecial_compile_wrong (names : List (Option MlString)) (trace : BackendCommon.Tra)
    (op : AstHOL.Op) (args : List FlatLang.Exp)
    (special : op = .opapp ∨ op = .opassign) (wrong : args.length ≠ 2) :
    compileExp names (.app trace (.src op) args) =
      .let .none (compileExps names args).reverse (.var .none 0) := by
  rcases special with rfl | rfl <;>
    rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩ <;>
    simp_all [compileExp, compileOp, compileExps, arg2]
  all_goals
    split
    · rename_i h
      have lengths := congrArg List.length h
      simp at lengths
    · rfl

/-- Wrong-arity application and assignment preserve any argument error; a
successful argument evaluation would contradict the source type-error exclusion. -/
theorem evaluate_binarySpecial_wrong {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : AstHOL.Op) (args : List FlatLang.Exp)
    (special : op = .opapp ∨ op = .opassign) (wrong : args.length ≠ 2)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src op) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src op) args] := by
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
  rw [binarySpecial_compile_wrong names trace op args special wrong, FlatSem.evaluate,
    ClosSem.evaluate, closFix]
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
        have arity := FlatSem.evaluate_length env source next args.reverse sourceArgs flatRun
        simp only [List.length_reverse] at arity
        have sourceWrong : sourceArgs.reverse.length ≠ 2 := by simpa [arity] using wrong
        have failure := binarySpecial_rejects next op sourceArgs.reverse special sourceWrong
        have fixed := flatFix
        rw [flatRun] at fixed
        apply False.elim
        apply notTypeError
        rw [FlatSem.evaluate, flatRun, fixed]
        rcases special with rfl | rfl
        · simp [failure.1 rfl]
        · simpa using failure.2 rfl

/-- The second source argument is evaluated first, so a non-type-error
binary application or assignment cannot have that argument fail with one. -/
theorem binarySpecial_argument_notTypeError {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (source : FlatSem.State C F) (trace : BackendCommon.Tra) (op : AstHOL.Op)
    (first second : FlatLang.Exp)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src op) [first, second]]).2 ≠
      .err (.abort .typeError)) :
    (FlatSem.evaluate env source [second]).2 ≠ .err (.abort .typeError) := by
  intro failure
  apply notTypeError
  rw [FlatSem.evaluate]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
  rw [(FlatSem.fixClock_evaluations env source [second, first] second []).1, FlatSem.evaluate]
  rw [(FlatSem.fixClock_evaluations env source [second] second []).1]
  simp only [failure]

/-- Assignment is simulated for any argument list, using the two operand
induction hypotheses only when the source arity is two. -/
theorem evaluate_assignment_any {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (operandSim : ∀ (expression : FlatLang.Exp) (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      expression ∈ args → StateRel next nextTarget → next.clock ≤ source.clock →
      (FlatSem.evaluate env next [expression]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values next nextTarget [expression])
    (states : StateRel source target)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .opassign) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .opassign) args] := by
  rcases args with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  · exact evaluate_binarySpecial_wrong env names values source target trace .opassign [] (Or.inr rfl) (by simp) argsSim notTypeError
  · exact evaluate_binarySpecial_wrong env names values source target trace .opassign [first] (Or.inr rfl) (by simp) argsSim notTypeError
  · exact evaluate_assignment env names values source target trace first second
      (operandSim second source target (by simp) states (le_refl _))
      (fun next nextTarget related bound => operandSim first next nextTarget (by simp) related bound) notTypeError
  · exact evaluate_binarySpecial_wrong env names values source target trace .opassign (first :: second :: third :: rest)
      (Or.inr rfl) (by simp) argsSim notTypeError

/-- Function application is simulated for any argument list using operand
and selected function-body induction hypotheses. -/
theorem evaluate_application_any {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (args : List FlatLang.Exp)
    (argsSim : (FlatSem.evaluate env source args.reverse).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source target args.reverse)
    (operandSim : ∀ (expression : FlatLang.Exp) (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      expression ∈ args → StateRel next nextTarget → next.clock ≤ source.clock →
      (FlatSem.evaluate env next [expression]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values next nextTarget [expression])
    (bodySim : ∀ (next : FlatSem.State C F) (nextTarget : ClosSem.State C F)
        (nextEnv : FlatSem.Environment FlatSem.Value) (body : FlatLang.Exp)
        (newNames : List (Option MlString)) (newValues : List ClosSem.Value),
      next.clock ≤ source.clock → next.clock ≠ 0 → EnvRel nextEnv newNames newValues → FlatProps.noMat body = true →
      StateRel (FlatSem.decClock next) (ClosSem.decClock 1 nextTarget) →
      (FlatSem.evaluate nextEnv (FlatSem.decClock next) [body]).2 ≠ .err (.abort .typeError) →
      EvalSim nextEnv newNames newValues (FlatSem.decClock next) (ClosSem.decClock 1 nextTarget) [body])
    (states : StateRel source target)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .opapp) args]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .opapp) args] := by
  rcases args with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩
  · exact evaluate_binarySpecial_wrong env names values source target trace .opapp [] (Or.inl rfl) (by simp) argsSim notTypeError
  · exact evaluate_binarySpecial_wrong env names values source target trace .opapp [first] (Or.inl rfl) (by simp) argsSim notTypeError
  · have secondNot := binarySpecial_argument_notTypeError env source trace .opapp first second notTypeError
    exact evaluate_application env names values source target trace first second
      (operandSim second source target (by simp) states (le_refl _) secondNot)
      (fun next nextTarget related bound => operandSim first next nextTarget (by simp) related bound)
      bodySim notTypeError
  · exact evaluate_binarySpecial_wrong env names values source target trace .opapp (first :: second :: third :: rest)
      (Or.inl rfl) (by simp) argsSim notTypeError

/-- Every source operator is simulated under the induction hypotheses for
its arguments, called bodies, thunk forcing, and installed declarations.
The synthetic thunk body and installed-declaration hypotheses still need to be
discharged by the general evaluator induction. This uses the preliminary
proof-side relations and is not a reviewed HOL port. -/
theorem evaluate_sourceOp {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (op : AstHOL.Op) (args : List FlatLang.Exp)
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
      ValueRel sourceValue targetValue → StateRel next nextTarget → next.clock ≤ source.clock →
      (FlatSem.evaluate ⟨[(ofString "f", sourceValue)]⟩ next
        [FlatSem.appUnit (.varLocal .none (ofString "f"))]).2 ≠ .err (.abort .typeError) →
      EvalSim ⟨[(ofString "f", sourceValue)]⟩ [some (ofString "f")] [targetValue] next nextTarget
        [FlatSem.appUnit (.varLocal .none (ofString "f"))])
    (decsSim : ∀ (decs : List FlatLang.Exp) (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      StateRel next nextTarget → next.clock < source.clock → FlatProps.noMatDecs decs = true →
      (FlatSem.evaluateDecs next decs).2 ≠ some (.abort .typeError) → DecUnitSim next nextTarget decs)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src op) args]).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src op) args] := by
  rcases directSourceOp_or_special op with direct | rfl | rfl | rfl | rfl
  · exact evaluate_directSourceOp env names values source target trace op args direct argsSim charInnerSim wordInnerSim notTypeError
  · exact evaluate_application_any env names values source target trace args argsSim operandSim bodySim states notTypeError
  · exact evaluate_assignment_any env names values source target trace args argsSim operandSim states notTypeError
  · exact evaluate_eval_related env names values source target trace args argsSim decsSim notTypeError
  · exact evaluate_force env names values source target trace args argsSim forceSim notTypeError

end Flapjack.Compiler.Backend.FlatToClos

import Flapjack.Compiler.Backend.FlatToClos.Proofs.StateRelation
import Flapjack.Compiler.Backend.Semantics.FlatSem.EvaluateLength
import Flapjack.Compiler.Backend.Semantics.ClosSem.EvaluateClock

/-! Initial cases of the proof-side flat-to-closure evaluator simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Relate expression results by relating returned lists and raised values,
while preserving aborts exactly. This proof-side relation and its semantic
carriers await correspondence review. -/
inductive EvalResultRel : Result (List FlatSem.Value) FlatSem.Value →
    Result (List ClosSem.Value) ClosSem.Value → Prop where
  | value {source target} (related : List.Forall₂ ValueRel source target) :
      EvalResultRel (.val source) (.val target)
  | raise {source target} (related : ValueRel source target) :
      EvalResultRel (.err (.raise source)) (.err (.raise target))
  | abort (error : Abort) : EvalResultRel (.err (.abort error)) (.err (.abort error))

/-- Evaluation of a flat expression list and its translation preserves the
proof-side state and result relations. -/
def EvalSim {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F) (expressions : List FlatLang.Exp) : Prop :=
  let sourceResult := FlatSem.evaluate env source expressions
  let targetResult := ClosSem.evaluate (compile names expressions) values target
  StateRel sourceResult.1 targetResult.2 ∧ EvalResultRel sourceResult.2 targetResult.1

/-- The empty expression list preserves the related state and returns empty
related lists. -/
theorem evaluate_nil {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (states : StateRel source target) : EvalSim env names values source target [] := by
  simpa [EvalSim, compile, compileExps, FlatSem.evaluate, ClosSem.evaluate] using
    And.intro states (EvalResultRel.value .nil)

/-- A successful flat local lookup reads the related closure environment at
the de Bruijn index chosen by compilation. -/
theorem evaluate_var {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (name : MlString) (value : FlatSem.Value)
    (states : StateRel source target) (environments : EnvRel env names values)
    (found : env.v.lookup name = some value) :
    EvalSim env names values source target [.varLocal trace name] := by
  obtain ⟨targetValue, targetFound, related⟩ := (envRel_iff_lookup _ _ _).1 environments name value found
  simpa [EvalSim, compile, compileExps, compileExp, FlatSem.evaluate, ClosSem.evaluate, found, targetFound]
    using And.intro states (EvalResultRel.value (.cons related .nil))

/-- Literal compilation evaluates to a related closure value without
changing either state. -/
theorem evaluate_lit {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (literal : Lit) (states : StateRel source target) :
    EvalSim env names values source target [.lit trace literal] := by
  cases literal <;>
    simp [EvalSim, compile, compileExps, compileExp, compileLit, FlatSem.evaluate,
      ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric,
      ClosSem.doIntApp, ClosSem.applyBlock, ClosSem.makeConst, states]
  all_goals first
    | exact EvalResultRel.value (.cons (ValueRel.int _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.char _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.string _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.word8 _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.word64 _) .nil)
    | exact EvalResultRel.value (.cons (ValueRel.float64 _) .nil)

/-- A match-free flat function compiles to a related unary closure when the
target supports unary calls. -/
theorem evaluate_fn {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace name : MlString) (body : FlatLang.Exp)
    (states : StateRel source target) (environments : EnvRel env names values)
    (safe : FlatProps.noMat body = true) :
    EvalSim env names values source target [.fn trace name body] := by
  have closure : ValueRel (.closure env name body) (.closure none [] values 1 (compileExp (some name :: names) body)) :=
    .closure environments safe
  have positive := states.1
  simp [EvalSim, compile, compileExps, compileExp, FlatSem.evaluate, ClosSem.evaluate.eq_def, positive, states,
    EvalResultRel.value (.cons closure .nil)]

/-- A related body simulation lifts through a raise, preserving an existing
error or relating the raised singleton value. -/
theorem evaluate_raise {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (body : FlatLang.Exp)
    (bodySim : EvalSim env names values source target [body]) :
    EvalSim env names values source target [.raise trace body] := by
  unfold EvalSim at bodySim ⊢
  simp only [compile, compileExps, compileExp] at bodySim ⊢
  rw [FlatSem.evaluate, ClosSem.evaluate]
  cases flatRun : FlatSem.evaluate env source [body] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names body] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at bodySim ⊢
      rcases bodySim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next body _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | nil => exact ⟨states, .raise head⟩
          | cons _ _ => simp at length

/-- Compose singleton and tail simulations for a nonempty tail. The tail
induction hypothesis is used only when the tail does not end in a source
type error, as in the original pass theorem. -/
theorem evaluate_cons {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (first second : FlatLang.Exp) (rest : List FlatLang.Exp)
    (firstSim : EvalSim env names values source target [first])
    (tailSim : ∀ (source' : FlatSem.State C F) (target' : ClosSem.State C F), StateRel source' target' →
      (FlatSem.evaluate env source' (second :: rest)).2 ≠ .err (.abort .typeError) →
      EvalSim env names values source' target' (second :: rest))
    (notTypeError : (FlatSem.evaluate env source (first :: second :: rest)).2 ≠ .err (.abort .typeError)) :
    EvalSim env names values source target (first :: second :: rest) := by
  have flatFix := (FlatSem.fixClock_evaluations env source [first] first []).1
  have closFix := ClosSem.fixClock_evaluate [compileExp names first] values target
  unfold EvalSim at firstSim ⊢
  simp only [compile, compileExps] at firstSim ⊢
  rw [FlatSem.evaluate, flatFix] at notTypeError ⊢
  rw [ClosSem.evaluate, closFix]
  cases flatRun : FlatSem.evaluate env source [first] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names first] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at firstSim notTypeError ⊢
      rcases firstSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next first _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | nil =>
            simp at notTypeError ⊢
            have tailNot : (FlatSem.evaluate env next (second :: rest)).2 ≠ .err (.abort .typeError) := by
              intro bad
              simp [bad] at notTypeError
            have tailRelated := tailSim next nextTarget states tailNot
            simp only [EvalSim, compile, compileExps] at tailRelated
            cases flatTail : FlatSem.evaluate env next (second :: rest) with
            | mk final flatResult =>
              cases closTail : ClosSem.evaluate (compileExp names second :: compileExps names rest) values nextTarget with
              | mk closResult finalTarget =>
                simp only [flatTail, closTail] at tailRelated ⊢
                rcases tailRelated with ⟨finalStates, finalResults⟩
                cases finalResults with
                | value tailValues => exact ⟨finalStates, .value (.cons head tailValues)⟩
                | raise valueRel => exact ⟨finalStates, .raise valueRel⟩
                | abort error => exact ⟨finalStates, .abort error⟩
          | cons _ _ => simp at length

end Flapjack.Compiler.Backend.FlatToClos

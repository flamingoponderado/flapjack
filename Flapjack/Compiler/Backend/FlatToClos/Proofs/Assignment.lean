import Flapjack.Compiler.Backend.FlatToClos.Proofs.MemoryExpressions
import Flapjack.Compiler.Backend.Semantics.ClosProps.Evaluate

/-! Scalar assignment in the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The inserted zero index is evaluated without changing state. -/
theorem evaluate_zero_index {C F : Type} (env : List ClosSem.Value) (state : ClosSem.State C F) :
    ClosSem.evaluate [.op .none (.intOp (.const 0)) []] env state = (.val [.number 0], state) := by
  simp [ClosSem.evaluate, ClosSem.fixClock, ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp]

/-- After the assignment value is evaluated, the inserted zero index
precedes the reference expression and does not alter its result or state. -/
theorem evaluate_assignment_args {C F : Type} (valueExpr refExpr : ClosLang.Exp)
    (env : List ClosSem.Value) (state next : ClosSem.State C F) (value : ClosSem.Value)
    (run : ClosSem.evaluate [valueExpr] env state = (.val [value], next)) :
    ClosSem.evaluate [valueExpr, .op .none (.intOp (.const 0)) [], refExpr] env state =
      match ClosSem.evaluate [refExpr] env next with
      | (.err error, last) => (.err error, last)
      | (.val values, last) => (.val (value :: .number 0 :: values), last) := by
  rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ run]
  rw [ClosProps.evaluate_cons_value _ _ _ _ _ _ (evaluate_zero_index env next)]
  cases result : ClosSem.evaluate [refExpr] env next with
  | mk outcome last => cases outcome <;> rfl

/-- A scalar assignment is simulated when its value and reference operands
are simulated in the source evaluation order. -/
theorem evaluate_assignment {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (reference value : FlatLang.Exp)
    (valueSim : EvalSim env names values source target [value])
    (referenceSim : ∀ (next : FlatSem.State C F) (nextTarget : ClosSem.State C F),
      StateRel next nextTarget → (FlatSem.evaluate env next [reference]).2 ≠ .err (.abort .typeError) →
      EvalSim env names values next nextTarget [reference])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.src .opassign) [reference, value]]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.src .opassign) [reference, value]] := by
  unfold EvalSim at valueSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, arg2, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append] at valueSim ⊢
  rw [FlatSem.evaluate] at notTypeError ⊢
  rw [ClosSem.evaluate, ClosSem.fixClock_evaluate]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append] at notTypeError ⊢
  rw [(FlatSem.fixClock_evaluations env source [value, reference] value []).1] at notTypeError ⊢
  rw [FlatSem.evaluate] at notTypeError ⊢
  rw [(FlatSem.fixClock_evaluations env source [value] value []).1] at notTypeError ⊢
  dsimp only at notTypeError ⊢
  cases flatValue : FlatSem.evaluate env source [value] with
  | mk next flatResult =>
    cases closValue : ClosSem.evaluate [compileExp names value] values target with
    | mk closResult nextTarget =>
      simp only [flatValue, closValue] at valueSim notTypeError ⊢
      rcases valueSim with ⟨states, results⟩
      cases results with
      | abort error =>
        rw [ClosProps.evaluate_cons_error _ _ _ _ _ _ closValue]
        exact ⟨states, .abort error⟩
      | raise related =>
        rw [ClosProps.evaluate_cons_error _ _ _ _ _ _ closValue]
        exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next value _ flatValue
        cases related with
        | nil => simp at length
        | cons valueRel tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            rename_i sourceValue targetValue
            rw [evaluate_assignment_args _ _ _ _ _ _ closValue]
            simp at notTypeError ⊢
            have refNot : (FlatSem.evaluate env next [reference]).2 ≠ .err (.abort .typeError) := by
              intro bad
              simp [bad] at notTypeError
            have refRelated := referenceSim next nextTarget states refNot
            simp only [EvalSim, compile, compileExps] at refRelated
            cases flatRef : FlatSem.evaluate env next [reference] with
            | mk after flatRefResult =>
              cases closRef : ClosSem.evaluate [compileExp names reference] values nextTarget with
              | mk closRefResult afterTarget =>
                simp only [flatRef, closRef] at refRelated notTypeError ⊢
                rcases refRelated with ⟨afterStates, refResults⟩
                cases refResults with
                | abort error => exact ⟨afterStates, .abort error⟩
                | raise valueRel => exact ⟨afterStates, .raise valueRel⟩
                | value referenceRel =>
                  have refLength := FlatSem.evaluate_singleton_length env next after reference _ flatRef
                  cases referenceRel with
                  | nil => simp at refLength
                  | cons head rest =>
                    cases rest with
                    | cons _ _ => simp at refLength
                    | nil =>
                      cases head <;> simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric,
                        FlatSem.doAppMemory] at notTypeError
                      case loc flag index =>
                        cases found : after.refs[index]? with
                        | none => simp [storeAssign, found] at notTypeError
                        | some old =>
                          cases old with
                          | w8array | varray | thunk => simp [storeAssign, found, storeValueSameType] at notTypeError
                          | refv old =>
                            obtain ⟨targetUpdated, sourceUpdate, targetUpdate, updatedStates⟩ :=
                              assignRef_related after afterTarget flag index old sourceValue targetValue afterStates valueRel found
                            simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppNumeric, sourceUpdate,
                              ClosSem.doApp, targetUpdate, updatedStates, FlatSem.unitValue, ClosSem.unitValue,
                              EvalResultRel.value (.cons (ValueRel.tuple .nil) .nil)]

end Flapjack.Compiler.Backend.FlatToClos

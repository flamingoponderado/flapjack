import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Global lookup cases for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- The target's first global is reserved, so a related source global at
index `n` appears at target index `n + 1`. -/
theorem globalLookup_related {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (index : Nat) (value : FlatSem.Value) (states : StateRel source target)
    (found : source.globals[index]? = some (some value)) :
    ∃ targetValue, ClosSem.getGlobal (index + 1) target.globals = some (some targetValue) ∧
      ValueRel value targetValue := by
  rcases states with ⟨_, _, _, _, nonempty, slots, _⟩
  obtain ⟨bound, valueEq⟩ := List.getElem?_eq_some_iff.mp found
  have targetBound : index < target.globals.tail.length := by
    have sameLength := slots.length_eq
    omega
  have relation := slots.get bound targetBound
  change optionalValueRel source.globals[index] target.globals.tail[index] at relation
  rw [valueEq] at relation
  cases targetFound : target.globals.tail[index] with
  | none =>
    rw [targetFound] at relation
    contradiction
  | some targetValue =>
    rw [targetFound] at relation
    refine ⟨targetValue, ?_, relation⟩
    cases globals : target.globals with
    | nil => simp [globals] at nonempty
    | cons first rest =>
      simp only [globals, List.tail_cons] at targetBound targetFound
      change rest[index]? = some (some targetValue)
      exact List.getElem?_eq_some_iff.mpr ⟨targetBound, targetFound⟩

/-- A successful global lookup reads the related target global and leaves
both states unchanged. -/
theorem evaluate_globalLookup {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (index : Nat) (states : StateRel source target)
    (notTypeError : (FlatSem.evaluate env source [.app trace (.globalVarLookup index) []]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.globalVarLookup index) []] := by
  cases slot : source.globals[index]? with
  | none => simp [FlatSem.evaluate, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp,
      FlatSem.doAppFlat, slot] at notTypeError
  | some slotValue =>
    cases slotValue with
    | none => simp [FlatSem.evaluate, FlatSem.fixClock, FlatSem.applyResult, FlatSem.doApp,
        FlatSem.doAppFlat, slot] at notTypeError
    | some value =>
      obtain ⟨targetValue, targetFound, related⟩ := globalLookup_related source target index value states slot
      simp [EvalSim, compile, compileExps, compileExp, compileOp, FlatSem.evaluate, FlatSem.fixClock,
        FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, slot, ClosSem.evaluate, ClosSem.fixClock,
        ClosSem.doApp, ClosSem.applyGlobal, targetFound, states,
        EvalResultRel.value (.cons related .nil)]

end Flapjack.Compiler.Backend.FlatToClos

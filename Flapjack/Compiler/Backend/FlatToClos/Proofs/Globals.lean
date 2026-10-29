import Flapjack.Compiler.Backend.FlatToClos.Proofs.EvaluateCases

/-! Global lookup cases for the proof-side flat-to-closure simulation. -/
namespace Flapjack.Compiler.Backend.FlatToClos
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Appending equally many empty global slots preserves the state relation. -/
theorem stateRel_allocGlobals {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (count : Nat) (states : StateRel source target) :
    StateRel { source with globals := source.globals ++ List.replicate count none }
      { target with globals := target.globals ++ List.replicate count none } := by
  rcases states with ⟨maxApp, ffi, clock, store, nonempty, slots, install⟩
  have blanks : List.Forall₂ optionalValueRel (List.replicate count none) (List.replicate count none) := by
    induction count with
    | zero => exact .nil
    | succ n ih => exact .cons trivial ih
  have appended := List.rel_append slots blanks
  refine ⟨maxApp, ffi, clock, store, ?_, ?_, install⟩
  · intro empty
    apply nonempty
    exact (List.append_eq_nil_iff.mp empty).1
  · cases globals : target.globals with
    | nil => simp [globals] at nonempty
    | cons first rest => simpa [globals] using appended

/-- Allocating empty globals produces unit and preserves related states. -/
theorem evaluate_globalAlloc {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (count : Nat) (states : StateRel source target) :
    EvalSim env names values source target [.app trace (.globalVarAlloc count) []] := by
  have updated := stateRel_allocGlobals source target count states
  have allocated : ClosSem.applyGlobal .allocGlobal [.number (Int.ofNat count)] target =
      some (ClosSem.unitValue, { target with globals := target.globals ++ List.replicate count none }) := by
    simp [ClosSem.applyGlobal]
  simp only [Int.ofNat_eq_natCast] at allocated
  simp [EvalSim, compile, compileExps, compileExp, compileOp, FlatSem.evaluate, FlatSem.fixClock,
    FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, ClosSem.evaluate, ClosSem.fixClock,
    ClosSem.doApp, ClosSem.applyNumeric, ClosSem.doIntApp, allocated, updated,
    FlatSem.unitValue, ClosSem.unitValue, EvalResultRel.value (.cons (ValueRel.tuple .nil) .nil)]

private theorem forall₂_set {α β : Type} {R : α → β → Prop} {left : List α} {right : List β}
    (related : List.Forall₂ R left right) (index : Nat) (bound : index < left.length)
    (a : α) (b : β) (head : R a b) : List.Forall₂ R (left.set index a) (right.set index b) := by
  induction related generalizing index with
  | nil => simp at bound
  | cons item tail ih =>
    cases index with
    | zero => simpa using List.Forall₂.cons head tail
    | succ index =>
      apply List.Forall₂.cons item
      apply ih
      simpa using bound

/-- Initializing corresponding empty slots preserves the global relation. -/
theorem stateRel_initGlobal {C F : Type} (source : FlatSem.State C F) (target : ClosSem.State C F)
    (index : Nat) (value : FlatSem.Value) (targetValue : ClosSem.Value)
    (states : StateRel source target) (related : ValueRel value targetValue)
    (empty : source.globals[index]? = some none) :
    ClosSem.getGlobal (index + 1) target.globals = some none ∧
    StateRel { source with globals := source.globals.set index (some value) }
      { target with globals := target.globals.set (index + 1) (some targetValue) } := by
  rcases states with ⟨maxApp, ffi, clock, store, nonempty, slots, install⟩
  obtain ⟨bound, slotEq⟩ := List.getElem?_eq_some_iff.mp empty
  have targetBound : index < target.globals.tail.length := by have := slots.length_eq; omega
  have relation := slots.get bound targetBound
  change optionalValueRel source.globals[index] target.globals.tail[index] at relation
  rw [slotEq] at relation
  have targetEq : target.globals.tail[index] = none := by
    cases found : target.globals.tail[index] <;> simp_all [optionalValueRel]
  have updated := forall₂_set slots index bound (some value) (some targetValue) related
  cases globals : target.globals with
  | nil => simp [globals] at nonempty
  | cons first rest =>
    simp only [globals, List.tail_cons] at targetBound targetEq updated
    have lookup : rest[index]? = some none := List.getElem?_eq_some_iff.mpr ⟨targetBound, targetEq⟩
    constructor
    · change rest[index]? = some none
      exact lookup
    · refine ⟨maxApp, ffi, clock, store, ?_, ?_, install⟩
      · simp
      · simpa [globals] using updated

/-- Initializing a global with a related operand returns unit in related
states. -/
theorem evaluate_globalInit {C F : Type} (env : FlatSem.Environment FlatSem.Value)
    (names : List (Option MlString)) (values : List ClosSem.Value)
    (source : FlatSem.State C F) (target : ClosSem.State C F)
    (trace : BackendCommon.Tra) (index : Nat) (argument : FlatLang.Exp)
    (argSim : EvalSim env names values source target [argument])
    (notTypeError : (FlatSem.evaluate env source [.app trace (.globalVarInit index) [argument]]).2 ≠
      .err (.abort .typeError)) :
    EvalSim env names values source target [.app trace (.globalVarInit index) [argument]] := by
  have flatFix := (FlatSem.fixClock_evaluations env source [argument] argument []).1
  have closFix := ClosSem.fixClock_evaluate [compileExp names argument] values target
  unfold EvalSim at argSim ⊢
  simp only [compile, compileExps, compileExp, compileOp, List.reverse_singleton] at argSim ⊢
  rw [FlatSem.evaluate] at notTypeError ⊢
  rw [ClosSem.evaluate, closFix]
  simp only [List.reverse_singleton, flatFix] at notTypeError ⊢
  cases flatRun : FlatSem.evaluate env source [argument] with
  | mk next flatResult =>
    cases closRun : ClosSem.evaluate [compileExp names argument] values target with
    | mk closResult nextTarget =>
      simp only [flatRun, closRun] at argSim notTypeError ⊢
      rcases argSim with ⟨states, results⟩
      cases results with
      | abort error => exact ⟨states, .abort error⟩
      | raise related => exact ⟨states, .raise related⟩
      | value related =>
        have length := FlatSem.evaluate_singleton_length env source next argument _ flatRun
        cases related with
        | nil => simp at length
        | cons head tail =>
          cases tail with
          | cons _ _ => simp at length
          | nil =>
            rename_i sourceValue targetValue
            cases slot : next.globals[index]? with
            | none => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, slot] at notTypeError
            | some slotValue =>
              cases slotValue with
              | some value => simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, slot] at notTypeError
              | none =>
                obtain ⟨targetSlot, updated⟩ := stateRel_initGlobal next nextTarget index sourceValue targetValue states head slot
                simp [FlatSem.applyResult, FlatSem.doApp, FlatSem.doAppFlat, slot, ClosSem.doApp,
                  ClosSem.applyGlobal, targetSlot, updated, FlatSem.unitValue, ClosSem.unitValue,
                  EvalResultRel.value (.cons (ValueRel.tuple .nil) .nil)]

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

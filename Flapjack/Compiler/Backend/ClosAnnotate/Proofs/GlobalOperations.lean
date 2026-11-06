import Flapjack.Compiler.Backend.ClosAnnotate.Proofs.Operations

/-! Global-store primitives under the annotation state relation. -/
namespace Flapjack.Compiler.Backend.ClosAnnotate
open Flapjack.Compiler.Backend.ClosSem Flapjack.Compiler.Backend.ClosProps

/-- Pointwise-related lists have related optional lookups, including absent
indices. -/
theorem optionRel_getElem {α β : Type} {R : α → β → Prop} (left : List α) (right : List β)
    (related : List.Forall₂ R left right) (index : Nat) :
    OptionRel R left[index]? right[index]? := by
  induction related generalizing index with
  | nil => cases index <;> trivial
  | cons head tail ih => cases index with
    | zero => exact head
    | succ index => exact ih index

/-- Updating corresponding positions in related lists preserves their
pointwise relation, including out-of-range updates. -/
theorem forall₂_set {α β : Type} {R : α → β → Prop} (left : List α) (right : List β)
    (related : List.Forall₂ R left right) (index : Nat) (x : α) (y : β) (xy : R x y) :
    List.Forall₂ R (left.set index x) (right.set index y) := by
  induction related generalizing index with
  | nil => cases index <;> exact .nil
  | cons head tail ih => cases index with
    | zero => exact .cons xy tail
    | succ index => exact .cons head (ih index)

/-- Updating the globals of two related states preserves their relation when
the updated lists are pointwise related. -/
theorem stateRel_withGlobals {C F : Type} (source target : State C F)
    (related : StateRel source target) (globals nextGlobals : List (Option Value))
    (globalsRel : List.Forall₂ (OptionRel ValueRel) globals nextGlobals) :
    StateRel { source with globals := globals } { target with globals := nextGlobals } := by
  exact ⟨related.1, related.2.1, related.2.2.1, related.2.2.2.1, related.2.2.2.2.1,
    globalsRel, related.2.2.2.2.2.2⟩

/-- Related global stores produce related values or fail in the same way. -/
theorem global_lookup_related {C F : Type} (source target : State C F)
    (related : StateRel source target) (index : Nat) :
    OptionRel ValueRel (getGlobal index source.globals).join (getGlobal index target.globals).join := by
  have lookup := optionRel_getElem source.globals target.globals related.2.2.2.2.2.1 index
  change OptionRel (OptionRel ValueRel) (getGlobal index source.globals) (getGlobal index target.globals) at lookup
  cases sourceLookup : getGlobal index source.globals with
  | none =>
    cases targetLookup : getGlobal index target.globals <;> simp [sourceLookup, targetLookup, OptionRel] at lookup ⊢
  | some sourceValue =>
    cases targetLookup : getGlobal index target.globals with
    | none => simp [sourceLookup, targetLookup, OptionRel] at lookup
    | some targetValue =>
      simpa [sourceLookup, targetLookup, OptionRel] using lookup

/-- A related optional lookup lifts to related primitive results. -/
theorem global_read_result {C F : Type} (source target : State C F) (related : StateRel source target)
    (index : Nat) :
    ∃ outcome,
      (match (getGlobal index target.globals).join.map (fun value => (value, target)) with
       | none => .err (.abort .typeError)
       | some pair => .val pair) = outcome ∧
      AppResultRel
        (match (getGlobal index source.globals).join.map (fun value => (value, source)) with
         | none => .err (.abort .typeError)
         | some pair => .val pair) outcome := by
  have lookup := global_lookup_related source target related index
  cases left : (getGlobal index source.globals).join with
  | none =>
    cases right : (getGlobal index target.globals).join with
    | none => exact ⟨.err (.abort .typeError), rfl, rfl⟩
    | some value => simp [left, right, OptionRel] at lookup
  | some value =>
    cases right : (getGlobal index target.globals).join with
    | none => simp [left, right, OptionRel] at lookup
    | some nextValue =>
      refine ⟨.val (nextValue, target), rfl, ?_⟩
      exact ⟨by simpa [left, right, OptionRel] using lookup, related⟩

/-- A source read and a target read of the same global index are simulated. -/
theorem primitiveSimulation_global {C F : Type} (index : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.globOp (.global index)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    obtain ⟨outcome, nextRun, rel⟩ := global_read_result source target states index
    refine ⟨outcome, ?_, ?_⟩
    · cases h : (getGlobal index target.globals).join <;> simpa [doApp, applyGlobal, h] using nextRun
    · cases h : (getGlobal index source.globals).join <;> simpa [doApp, applyGlobal, h] using rel
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | number number =>
        by_cases negative : number < 0
        · refine ⟨.err (.abort .typeError), ?_, ?_⟩ <;>
            simp [doApp, applyGlobal, negative, AppResultRel, ResultRel]
        · obtain ⟨outcome, nextRun, rel⟩ := global_read_result source target states number.toNat
          refine ⟨outcome, ?_, ?_⟩
          · cases h : (getGlobal number.toNat target.globals).join <;> simpa [doApp, applyGlobal, negative, h] using nextRun
          · cases h : (getGlobal number.toNat source.globals).join <;> simpa [doApp, applyGlobal, negative, h] using rel
      | _ =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal], by simp [doApp, applyGlobal, AppResultRel, ResultRel]⟩
    | cons head tail =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal], by simp [doApp, applyGlobal, AppResultRel, ResultRel]⟩

/-- Writing related values to the same empty global slot preserves states. -/
theorem global_set_result {C F : Type} (source target : State C F) (states : StateRel source target)
    (index : Nat) (value nextValue : Value) (valuesRel : ValueRel value nextValue) :
    ∃ outcome, doApp (.globOp (.setGlobal index)) [nextValue] target = outcome ∧
      AppResultRel (doApp (.globOp (.setGlobal index)) [value] source) outcome := by
  have lookup := optionRel_getElem source.globals target.globals states.2.2.2.2.2.1 index
  change OptionRel (OptionRel ValueRel) (getGlobal index source.globals) (getGlobal index target.globals) at lookup
  cases left : getGlobal index source.globals with
  | none =>
    cases right : getGlobal index target.globals with
    | none =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal, right], by
        simp [doApp, applyGlobal, left, AppResultRel, ResultRel]⟩
    | some x => simp [left, right, OptionRel] at lookup
  | some x =>
    cases right : getGlobal index target.globals with
    | none => simp [left, right, OptionRel] at lookup
    | some y =>
      cases x with
      | none =>
        cases y with
        | none =>
          have globalsRel := forall₂_set source.globals target.globals states.2.2.2.2.2.1
            index (some value) (some nextValue) valuesRel
          have nextStates := stateRel_withGlobals source target states _ _ globalsRel
          refine ⟨.val (unitValue, { target with globals := target.globals.set index (some nextValue) }), ?_, ?_⟩
          · simp [doApp, applyGlobal, right]
          · simpa [doApp, applyGlobal, left, AppResultRel, unitValue] using
              And.intro (ValueRel.block 0 [] [] .nil) nextStates
        | some value => simp [left, right, OptionRel] at lookup
      | some value =>
        cases y with
        | none => simp [left, right, OptionRel] at lookup
        | some nextValue =>
          exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal, right], by
            simp [doApp, applyGlobal, left, AppResultRel, ResultRel]⟩

/-- Global writes preserve the primitive relation for every argument list. -/
theorem primitiveSimulation_setGlobal {C F : Type} (index : Nat) :
    PrimitiveSimulation (C := C) (F := F) (.globOp (.setGlobal index)) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal], by simp [doApp, applyGlobal, AppResultRel, ResultRel]⟩
  | cons head tail =>
    cases tail with
    | nil => exact global_set_result source target states index _ _ head
    | cons first rest =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal], by simp [doApp, applyGlobal, AppResultRel, ResultRel]⟩

/-- Appending equally many empty global slots preserves state relatedness. -/
theorem stateRel_allocGlobals {C F : Type} (source target : State C F) (states : StateRel source target)
    (count : Nat) :
    StateRel { source with globals := source.globals ++ List.replicate count none }
      { target with globals := target.globals ++ List.replicate count none } := by
  apply stateRel_withGlobals source target states
  apply List.rel_append states.2.2.2.2.2.1
  induction count with
  | zero => exact .nil
  | succ count ih => simpa only [List.replicate_succ] using List.Forall₂.cons (by trivial) ih

/-- Allocating global slots preserves the primitive relation. -/
theorem primitiveSimulation_allocGlobal {C F : Type} :
    PrimitiveSimulation (C := C) (F := F) (.globOp .allocGlobal) := by
  intro values nextValues source target valuesRel states
  cases valuesRel with
  | nil =>
    exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal], by simp [doApp, applyGlobal, AppResultRel, ResultRel]⟩
  | cons head tail =>
    cases tail with
    | nil =>
      cases head with
      | number number =>
        by_cases negative : number < 0
        · exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal, negative], by
            simp [doApp, applyGlobal, negative, AppResultRel, ResultRel]⟩
        · refine ⟨.val (unitValue, { target with globals := target.globals ++ List.replicate number.toNat none }), ?_, ?_⟩
          · simp [doApp, applyGlobal, negative]
          · simpa [doApp, applyGlobal, negative, AppResultRel, unitValue] using
              And.intro (ValueRel.block 0 [] [] .nil) (stateRel_allocGlobals source target states number.toNat)
      | _ =>
        exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal], by simp [doApp, applyGlobal, AppResultRel, ResultRel]⟩
    | cons first rest =>
      exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal], by simp [doApp, applyGlobal, AppResultRel, ResultRel]⟩

/-- Every global operation preserves the candidate primitive simulation. -/
theorem primitiveSimulation_globalOp {C F : Type} (op : ClosLang.GlobOp) :
    PrimitiveSimulation (C := C) (F := F) (.globOp op) := by
  cases op with
  | global index => exact primitiveSimulation_global index
  | setGlobal index => exact primitiveSimulation_setGlobal index
  | allocGlobal => exact primitiveSimulation_allocGlobal
  | globalsPtr | setGlobalsPtr =>
    intro values nextValues source target valuesRel states
    exact ⟨.err (.abort .typeError), by simp [doApp, applyGlobal], by simp [doApp, applyGlobal, AppResultRel, ResultRel]⟩

end Flapjack.Compiler.Backend.ClosAnnotate

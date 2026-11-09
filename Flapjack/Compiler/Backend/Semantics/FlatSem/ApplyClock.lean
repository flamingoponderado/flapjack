module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply
public import Flapjack.FfiHOL

@[expose] public section

/-! Clock, evaluation-configuration, and I/O-event preservation for the flat primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Flat-specific primitive operations preserve the clock and evaluation configuration. -/
private theorem doAppFlat_stable {C F : Type} (state next : State C F) (op : FlatLang.Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppFlat state op values = some (some (next, result))) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  cases op <;> simp only [doAppFlat] at run
  all_goals repeat' split at run
  all_goals simp_all
  all_goals try (rcases run with ⟨h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩)
  all_goals rcases run with ⟨_, _, h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩

/-- The source numeric projection leaves the flat state unchanged. -/
private theorem applyNumericProjection_stable {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (errorValue : Value) (result : Result Value Value)
    (run : applyNumericProjection state op values errorValue = some (next, result)) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  unfold applyNumericProjection at run
  cases call : SemanticPrimitivesHOL.doApp ([], state.ffi) op (values.map flatToValue) with
  | none => simp [call] at run
  | some pair =>
    obtain ⟨sourceState, sourceResult⟩ := pair
    cases sourceResult with
    | val value => simp [call] at run; rcases run with ⟨h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩
    | err error =>
      cases error <;> simp [call] at run <;> rcases run with ⟨h, _⟩ <;> subst next <;> exact ⟨rfl, rfl, List.prefix_refl _⟩

/-- Numeric and comparison primitives leave the state unchanged. -/
private theorem doAppNumeric_stable {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppNumeric state op values = some (some (next, result))) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  cases op <;> simp only [doAppNumeric] at run
  all_goals try (simp only [Option.some.injEq] at run; exact applyNumericProjection_stable state next _ values _ result run)
  all_goals repeat' split at run
  all_goals simp_all
  all_goals try (rcases run with ⟨h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩)

/-- Bounds failures preserve the clock and evaluation configuration. -/
private theorem boundsFailure_stable {C F : Type} (state next : State C F) (unsafeOp : Bool)
    (result : Result Value Value) (run : boundsFailure state unsafeOp = some (next, result)) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  cases unsafeOp <;> simp [boundsFailure] at run
  rcases run with ⟨h, _⟩
  subst next
  exact ⟨rfl, rfl, List.prefix_refl _⟩

/-- Indexed reads preserve the clock and evaluation configuration, including bounds errors. -/
private theorem readIndexed_stable {C F α : Type} (state next : State C F) (unsafeOp : Bool)
    (items : List α) (index : Int) (toValue : α → Value) (result : Result Value Value)
    (run : readIndexed state unsafeOp items index toValue = some (next, result)) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  unfold readIndexed at run
  split at run
  · exact boundsFailure_stable state next unsafeOp result run
  · split at run
    · exact boundsFailure_stable state next unsafeOp result run
    · simp at run
      rcases run with ⟨h, _⟩
      subst next
      exact ⟨rfl, rfl, List.prefix_refl _⟩

/-- Indexed writes update only the store, including checked bounds errors. -/
private theorem updateIndexed_stable {C F α : Type} (state next : State C F) (unsafeOp : Bool)
    (address : Nat) (items : List α) (index : Int) (value : α)
    (asStore : List α → StoreValue Value) (result : Result Value Value)
    (run : updateIndexed state unsafeOp address items index value asStore = some (next, result)) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  unfold updateIndexed at run
  split at run
  · exact boundsFailure_stable state next unsafeOp result run
  · cases assigned : storeAssign address (asStore (items.set index.toNat value)) state.refs with
    | none => simp [assigned] at run
    | some refs =>
      simp [assigned] at run
      rcases run with ⟨h, _⟩
      subst next
      exact ⟨rfl, rfl, List.prefix_refl _⟩

/-- Reference and array primitives preserve the clock and evaluation configuration. -/
private theorem doAppMemory_stable {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppMemory state op values = some (some (next, result))) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  cases op <;> simp only [doAppMemory] at run
  all_goals repeat' split at run
  all_goals try (simp only [Option.some.injEq] at run; exact readIndexed_stable state next _ _ _ _ result run)
  all_goals try (simp only [Option.some.injEq] at run; exact updateIndexed_stable state next _ _ _ _ _ _ result run)
  all_goals try (simp only [Option.some.injEq] at run; exact boundsFailure_stable state next _ result run)
  all_goals simp_all [storeAlloc]
  all_goals try (rcases run with ⟨h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩)
  all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at run
  all_goals rcases run with ⟨_, _, h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩

/-- String, list, vector, thunk and FFI primitives preserve the clock and evaluation configuration. -/
private theorem doAppData_stable {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppData state op values = some (some (next, result))) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  cases op <;> simp only [doAppData] at run
  all_goals repeat' split at run
  all_goals try (simp only [Option.some.injEq] at run; exact readIndexed_stable state next _ _ _ _ result run)
  all_goals simp_all [storeAlloc, Option.bind_eq_some_iff]
  all_goals try (rcases run with ⟨h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩)
  all_goals try (rcases run with ⟨_, _, _, _, h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩)
  all_goals rcases run with ⟨_, _, h, _⟩; subst next
  all_goals refine ⟨rfl, rfl, ?_⟩
  all_goals apply Flapjack.callFFIHOL_return_ioEvents_prefix
  all_goals assumption

/-- Copy and XOR primitives preserve the clock and evaluation configuration. -/
private theorem doAppCopy_stable {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppCopy state op values = some (some (next, result))) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  cases op <;> simp only [doAppCopy] at run
  all_goals repeat' split at run
  all_goals try (simp only [Option.some.injEq] at run; exact boundsFailure_stable state next _ result run)
  all_goals simp_all [Option.bind_eq_some_iff]
  all_goals try (rcases run with ⟨h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩)
  all_goals try (rcases run with ⟨_, _, _, _, h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩)
  all_goals rcases run with ⟨_, _, h, _⟩; subst next; exact ⟨rfl, rfl, List.prefix_refl _⟩

private theorem getD_some {α : Type} (value : Option (Option α)) (result : α)
    (h : value.getD none = some result) : value = some (some result) := by
  cases value <;> simp_all

/-- Flapjack infrastructure: the primitive dispatcher jointly preserves clock
and evaluation configuration while extending I/O events. This shared invariant
proves the separate HOL primitive preservation results. -/
theorem doApp_stableAndIo {C F : Type} (state next : State C F) (op : FlatLang.Op)
    (values : List Value) (result : Result Value Value)
    (run : doApp state op values = some (next, result)) : next.clock = state.clock ∧ next.evalConfig = state.evalConfig ∧ state.ffi.ioEvents <+: next.ffi.ioEvents := by
  cases op with
  | src sourceOp =>
    unfold doApp at run
    cases numeric : doAppNumeric state sourceOp values with
    | some outcome =>
      have h : doAppNumeric state sourceOp values = some (some (next, result)) := by
        simpa [numeric] using run
      exact doAppNumeric_stable state next sourceOp values result h
    | none =>
      cases memory : doAppMemory state sourceOp values with
      | some outcome =>
        have h : doAppMemory state sourceOp values = some (some (next, result)) := by
          simpa [numeric, memory] using run
        exact doAppMemory_stable state next sourceOp values result h
      | none =>
        cases data : doAppData state sourceOp values with
        | some outcome =>
          have h : doAppData state sourceOp values = some (some (next, result)) := by
            simpa [numeric, memory, data] using run
          exact doAppData_stable state next sourceOp values result h
        | none =>
          have h : doAppCopy state sourceOp values = some (some (next, result)) := by
            cases copy : doAppCopy state sourceOp values <;> simp_all
          exact doAppCopy_stable state next sourceOp values result h
  | globalVarAlloc _ | globalVarInit _ | globalVarLookup _ | tagLenEq _ _ | lenEq _ | el _ | id =>
    simp only [doApp] at run
    exact doAppFlat_stable state next _ values result (getD_some _ _ run)

/-- The clock and configuration projections of the shared dispatcher invariant. -/
theorem doApp_stable {C F : Type} (state next : State C F) (op : FlatLang.Op)
    (values : List Value) (result : Result Value Value)
    (run : doApp state op values = some (next, result)) :
    next.clock = state.clock ∧ next.evalConfig = state.evalConfig := by
  have stable := doApp_stableAndIo state next op values result run
  exact ⟨stable.1, stable.2.1⟩

/-- A successful primitive application preserves the clock. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "do_app_const"]
theorem doApp_const {C F : Type} (state : State C F) (op : FlatLang.Op)
    (values : List Value) (next : State C F) (result : Result Value Value) :
    doApp state op values = some (next, result) → state.clock = next.clock := by
  intro run
  exact (doApp_stable state next op values result run).1.symm

end Flapjack.Compiler.Backend.FlatSem

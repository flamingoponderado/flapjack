import Flapjack.Compiler.Backend.Semantics.FlatSem.Apply

/-! Clock preservation for the assembled flat primitive dispatcher. These
lemmas are untagged pending full review of the underlying dispatcher. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Flat-specific primitive operations do not change the clock. -/
theorem doAppFlat_clock {C F : Type} (state next : State C F) (op : FlatLang.Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppFlat state op values = some (some (next, result))) :
    next.clock = state.clock := by
  cases op <;> simp only [doAppFlat] at run
  all_goals repeat' split at run
  all_goals simp_all
  all_goals try (rcases run with ⟨h, _⟩; subst next; rfl)
  all_goals rcases run with ⟨_, _, h, _⟩; subst next; rfl

/-- The source numeric projection leaves the flat state unchanged. -/
theorem applyNumericProjection_clock {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (errorValue : Value) (result : Result Value Value)
    (run : applyNumericProjection state op values errorValue = some (next, result)) :
    next.clock = state.clock := by
  unfold applyNumericProjection at run
  cases call : SemanticPrimitivesHOL.doApp ([], state.ffi) op (values.map flatToValue) with
  | none => simp [call] at run
  | some pair =>
    obtain ⟨sourceState, sourceResult⟩ := pair
    cases sourceResult with
    | val value => simp [call] at run; rcases run with ⟨h, _⟩; subst next; rfl
    | err error =>
      cases error <;> simp [call] at run <;> rcases run with ⟨h, _⟩ <;> subst next <;> rfl

/-- Numeric and comparison primitives leave the state unchanged. -/
theorem doAppNumeric_clock {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppNumeric state op values = some (some (next, result))) :
    next.clock = state.clock := by
  cases op <;> simp only [doAppNumeric] at run
  all_goals try (simp only [Option.some.injEq] at run; exact applyNumericProjection_clock state next _ values _ result run)
  all_goals repeat' split at run
  all_goals simp_all
  all_goals try (rcases run with ⟨h, _⟩; subst next; rfl)

/-- Bounds failures do not change the state. -/
theorem boundsFailure_clock {C F : Type} (state next : State C F) (unsafeOp : Bool)
    (result : Result Value Value) (run : boundsFailure state unsafeOp = some (next, result)) :
    next.clock = state.clock := by
  cases unsafeOp <;> simp [boundsFailure] at run
  rcases run with ⟨h, _⟩
  subst next
  rfl

/-- Indexed reads do not change the state, including bounds errors. -/
theorem readIndexed_clock {C F α : Type} (state next : State C F) (unsafeOp : Bool)
    (items : List α) (index : Int) (toValue : α → Value) (result : Result Value Value)
    (run : readIndexed state unsafeOp items index toValue = some (next, result)) :
    next.clock = state.clock := by
  unfold readIndexed at run
  split at run
  · exact boundsFailure_clock state next unsafeOp result run
  · split at run
    · exact boundsFailure_clock state next unsafeOp result run
    · simp at run
      rcases run with ⟨h, _⟩
      subst next
      rfl

/-- Indexed writes update only the store, including checked bounds errors. -/
theorem updateIndexed_clock {C F α : Type} (state next : State C F) (unsafeOp : Bool)
    (address : Nat) (items : List α) (index : Int) (value : α)
    (asStore : List α → StoreValue Value) (result : Result Value Value)
    (run : updateIndexed state unsafeOp address items index value asStore = some (next, result)) :
    next.clock = state.clock := by
  unfold updateIndexed at run
  split at run
  · exact boundsFailure_clock state next unsafeOp result run
  · cases assigned : storeAssign address (asStore (items.set index.toNat value)) state.refs with
    | none => simp [assigned] at run
    | some refs =>
      simp [assigned] at run
      rcases run with ⟨h, _⟩
      subst next
      rfl

/-- Reference and array primitives preserve the clock. -/
theorem doAppMemory_clock {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppMemory state op values = some (some (next, result))) :
    next.clock = state.clock := by
  cases op <;> simp only [doAppMemory] at run
  all_goals repeat' split at run
  all_goals try (simp only [Option.some.injEq] at run; exact readIndexed_clock state next _ _ _ _ result run)
  all_goals try (simp only [Option.some.injEq] at run; exact updateIndexed_clock state next _ _ _ _ _ _ result run)
  all_goals try (simp only [Option.some.injEq] at run; exact boundsFailure_clock state next _ result run)
  all_goals simp_all [storeAlloc]
  all_goals try (rcases run with ⟨h, _⟩; subst next; rfl)
  all_goals simp only [Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at run
  all_goals rcases run with ⟨_, _, h, _⟩; subst next; rfl

/-- String, list, vector, thunk and FFI primitives preserve the clock. -/
theorem doAppData_clock {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppData state op values = some (some (next, result))) :
    next.clock = state.clock := by
  cases op <;> simp only [doAppData] at run
  all_goals repeat' split at run
  all_goals try (simp only [Option.some.injEq] at run; exact readIndexed_clock state next _ _ _ _ result run)
  all_goals simp_all [storeAlloc, Option.bind_eq_some_iff]
  all_goals try (rcases run with ⟨h, _⟩; subst next; rfl)
  all_goals try (rcases run with ⟨_, _, _, _, h, _⟩; subst next; rfl)
  all_goals rcases run with ⟨_, _, h, _⟩; subst next; rfl

/-- Copy and XOR primitives preserve the clock. -/
theorem doAppCopy_clock {C F : Type} (state next : State C F) (op : Op)
    (values : List Value) (result : Result Value Value)
    (run : doAppCopy state op values = some (some (next, result))) :
    next.clock = state.clock := by
  cases op <;> simp only [doAppCopy] at run
  all_goals repeat' split at run
  all_goals try (simp only [Option.some.injEq] at run; exact boundsFailure_clock state next _ result run)
  all_goals simp_all [Option.bind_eq_some_iff]
  all_goals try (rcases run with ⟨h, _⟩; subst next; rfl)
  all_goals try (rcases run with ⟨_, _, _, _, h, _⟩; subst next; rfl)
  all_goals rcases run with ⟨_, _, h, _⟩; subst next; rfl

private theorem getD_some {α : Type} (value : Option (Option α)) (result : α)
    (h : value.getD none = some result) : value = some (some result) := by
  cases value <;> simp_all

/-- The assembled flat primitive dispatcher preserves the clock. This is an
untagged result about the dispatcher pending its full HOL source review. -/
theorem doApp_clock {C F : Type} (state next : State C F) (op : FlatLang.Op)
    (values : List Value) (result : Result Value Value)
    (run : doApp state op values = some (next, result)) : next.clock = state.clock := by
  cases op with
  | src sourceOp =>
    unfold doApp at run
    cases numeric : doAppNumeric state sourceOp values with
    | some outcome =>
      have h : doAppNumeric state sourceOp values = some (some (next, result)) := by
        simpa [numeric] using run
      exact doAppNumeric_clock state next sourceOp values result h
    | none =>
      cases memory : doAppMemory state sourceOp values with
      | some outcome =>
        have h : doAppMemory state sourceOp values = some (some (next, result)) := by
          simpa [numeric, memory] using run
        exact doAppMemory_clock state next sourceOp values result h
      | none =>
        cases data : doAppData state sourceOp values with
        | some outcome =>
          have h : doAppData state sourceOp values = some (some (next, result)) := by
            simpa [numeric, memory, data] using run
          exact doAppData_clock state next sourceOp values result h
        | none =>
          have h : doAppCopy state sourceOp values = some (some (next, result)) := by
            cases copy : doAppCopy state sourceOp values <;> simp_all
          exact doAppCopy_clock state next sourceOp values result h
  | globalVarAlloc _ | globalVarInit _ | globalVarLookup _ | tagLenEq _ _ | lenEq _ | el _ | id =>
    simp only [doApp] at run
    exact doAppFlat_clock state next _ values result (getD_some _ _ run)

end Flapjack.Compiler.Backend.FlatSem

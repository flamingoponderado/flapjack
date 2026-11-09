module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyClock

@[expose] public section

/-! Clock changes commute with the complete flat primitive dispatcher. The
private lemmas establish the result for its component dispatchers. -/
namespace Flapjack.Compiler.Backend.FlatProps
open Flapjack.Compiler.Backend.FlatSem
open Flapjack.SemanticPrimitivesHOL (Result)
private def clockOption {C F : Type} (k : Nat) : Option (State C F × Result Value Value) → Option (State C F × Result Value Value) :=
  Option.map (fun (s,r) => ({ s with clock := k },r))
private def clockNested {C F : Type} (k : Nat) : Option (Option (State C F × Result Value Value)) → Option (Option (State C F × Result Value Value)) :=
  Option.map (clockOption k)
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem flatClock {C F : Type} (state : State C F) (op : FlatLang.Op) (values : List Value) (k : Nat) :
    doAppFlat { state with clock := k } op values = clockNested k (doAppFlat state op values) := by
  cases op <;> simp only [doAppFlat, clockNested, clockOption, Option.map]
  all_goals repeat' split <;> simp_all
  all_goals split <;> try simp_all
  all_goals repeat' split <;> try simp_all
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem projectionClock {C F : Type} (state : State C F) (op : Flapjack.AstHOL.Op) (values : List Value)
    (errorValue : Value) (k : Nat) :
    applyNumericProjection { state with clock := k } op values errorValue =
      clockOption k (applyNumericProjection state op values errorValue) := by
  unfold applyNumericProjection
  cases h : Flapjack.SemanticPrimitivesHOL.doApp ([], state.ffi) op (values.map flatToValue) with
  | none => simp [clockOption]
  | some pair =>
    obtain ⟨sourceState, result⟩ := pair
    cases result with
    | val value => simp [clockOption]
    | err error => cases error <;> simp [clockOption]
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem numericClock {C F : Type} (state : State C F) (op : Flapjack.AstHOL.Op) (values : List Value) (k : Nat) :
    doAppNumeric { state with clock := k } op values = clockNested k (doAppNumeric state op values) := by
  cases op <;> simp only [doAppNumeric, clockNested, Option.map]
  all_goals try rw [projectionClock]
  all_goals try rfl
  all_goals repeat' split <;> simp_all [clockOption]
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem boundsClock {C F : Type} (state : State C F) (unsafeOp : Bool) (k : Nat) :
    boundsFailure { state with clock := k } unsafeOp = clockOption k (boundsFailure state unsafeOp) := by
  cases unsafeOp <;> rfl
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem readClock {C F α : Type} (state : State C F) (unsafeOp : Bool)
    (items : List α) (index : Int) (toValue : α → Value) (k : Nat) :
    readIndexed { state with clock := k } unsafeOp items index toValue =
      clockOption k (readIndexed state unsafeOp items index toValue) := by
  unfold readIndexed
  split
  · exact boundsClock state unsafeOp k
  · cases items[index.toNat]? <;> simp [boundsClock, clockOption]
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem updateClock {C F α : Type} (state : State C F) (unsafeOp : Bool)
    (address : Nat) (items : List α) (index : Int) (value : α)
    (asStore : List α → Flapjack.SemanticPrimitivesHOL.StoreValue Value) (k : Nat) :
    updateIndexed { state with clock := k } unsafeOp address items index value asStore =
      clockOption k (updateIndexed state unsafeOp address items index value asStore) := by
  unfold updateIndexed
  split
  · exact boundsClock state unsafeOp k
  · cases Flapjack.SemanticPrimitivesHOL.storeAssign address (asStore (items.set index.toNat value)) state.refs <;> rfl
set_option maxHeartbeats 1200000 in
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem memoryClock {C F : Type} (state : State C F) (op : Flapjack.AstHOL.Op) (values : List Value) (k : Nat) :
    doAppMemory { state with clock := k } op values = clockNested k (doAppMemory state op values) := by
  cases op <;> simp only [doAppMemory, clockNested, Option.map]
  all_goals repeat' split <;> simp_all [boundsClock, readClock, updateClock, clockOption]
  all_goals try rfl
  all_goals simp only [Option.bind_eq_bind]
  all_goals split <;> rfl
set_option maxHeartbeats 1200000 in
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem dataClock {C F : Type} (state : State C F) (op : Flapjack.AstHOL.Op) (values : List Value) (k : Nat) :
    doAppData { state with clock := k } op values = clockNested k (doAppData state op values) := by
  cases op <;> simp only [doAppData, clockNested, Option.map]
  all_goals repeat' split <;> simp_all [readClock, clockOption]
  all_goals try rfl
  all_goals try simp only [Option.bind_eq_bind]
  all_goals repeat' split <;> try simp_all
  all_goals simp only [Option.bind]
  all_goals repeat' split <;> try simp_all
set_option maxHeartbeats 1200000 in
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem copyClock {C F : Type} (state : State C F) (op : Flapjack.AstHOL.Op) (values : List Value) (k : Nat) :
    doAppCopy { state with clock := k } op values = clockNested k (doAppCopy state op values) := by
  cases op <;> simp only [doAppCopy, clockNested, Option.map]
  all_goals repeat' split <;> simp_all [boundsClock, clockOption]
  all_goals try rfl
  all_goals try simp only [Option.bind_eq_bind]
  all_goals repeat' split <;> try simp_all
  all_goals simp only [Option.bind]
  all_goals repeat' split <;> try simp_all
set_option maxHeartbeats 1200000 in
/-- Flapjack infrastructure for the full HOL primitive clock-change result. -/
private theorem doAppSetClock {C F : Type} (state : State C F) (op : FlatLang.Op) (values : List Value) (k : Nat) :
    doApp { state with clock := k } op values = clockOption k (doApp state op values) := by
  cases op with
  | src source =>
    simp only [doApp, numericClock]
    cases hnum : doAppNumeric state source values with
    | some outcome => simp [clockNested]
    | none =>
      simp only [clockNested, Option.map]
      rw [memoryClock]
      cases hmem : doAppMemory state source values with
      | some outcome => simp [clockNested]
      | none =>
        simp only [clockNested, Option.map]
        rw [dataClock]
        cases hdata : doAppData state source values with
        | some outcome => simp [clockNested]
        | none =>
          simp only [clockNested, Option.map]
          rw [copyClock]
          cases hcopy : doAppCopy state source values <;> simp [clockNested, clockOption]
  | globalVarAlloc n | globalVarInit n | globalVarLookup n | el n =>
    simp only [doApp, flatClock]
    cases h : doAppFlat state _ values <;> simp [clockNested, clockOption]
  | tagLenEq n m =>
    simp only [doApp, flatClock]
    cases h : doAppFlat state _ values <;> simp [clockNested, clockOption]
  | lenEq n =>
    simp only [doApp, flatClock]
    cases h : doAppFlat state _ values <;> simp [clockNested, clockOption]
  | id =>
    simp only [doApp, flatClock]
    cases h : doAppFlat state _ values <;> simp [clockNested, clockOption]
/-- A successful primitive application commutes with adding to the clock. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "do_app_add_to_clock"]
theorem doApp_addToClock {C F : Type} (state : State C F) (op : FlatLang.Op) (values : List Value)
    (next : State C F) (result : Result Value Value) (extra : Nat)
    (run : doApp state op values = some (next, result)) :
    doApp { state with clock := state.clock + extra } op values =
      some ({ next with clock := next.clock + extra }, result) := by
  have clock := (doApp_stable state next op values result run).1
  simpa [clockOption, run, clock] using doAppSetClock state op values (state.clock + extra)

/-- Primitive application failure is unchanged when the clock is increased. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "do_app_add_to_clock_NONE"]
theorem doApp_addToClock_none {C F : Type} (state : State C F) (op : FlatLang.Op) (values : List Value) (extra : Nat)
    (run : doApp state op values = none) :
    doApp { state with clock := state.clock + extra } op values = none := by
  simpa [clockOption, run] using doAppSetClock state op values (state.clock + extra)

/-- Updating a flat state clock leaves its FFI state unchanged. -/
@[hol "cakeml/compiler/backend/semantics/flatPropsScript.sml" "with_clock_ffi"]
theorem withClock_ffi {C F : Type} (state : State C F) (clock : Nat) :
    ({ state with clock := clock }).ffi = state.ffi := rfl

end Flapjack.Compiler.Backend.FlatProps

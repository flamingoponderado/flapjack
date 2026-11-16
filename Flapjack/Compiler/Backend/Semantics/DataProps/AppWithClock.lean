module

public import Flapjack.Compiler.Backend.Semantics.DataSem.ApplyFields
public import Flapjack.Compiler.Backend.Semantics.DataProps.InitialStateLaws

@[expose] public section

/-!
# Primitive application under a clock update

The data-language primitive dispatcher reads only fields other than the
evaluation clock, so replacing the clock of the input state commutes with the
whole application. This module builds that fact from the space, stack, limit,
auxiliary-application and installation stages, in the order the dispatcher
composes them.
-/
namespace Flapjack.Compiler.Backend.DataProps
open Flapjack Flapjack.SemanticPrimitivesHOL
open Flapjack.SemanticPrimitivesProps
open Flapjack.Compiler.Backend.DataSem

/-- Heap-space consumption compares and updates only the space field. -/
theorem consumeSpace_clock {C F : Type} (amount : Nat) (state : State C F) (clock : Nat) :
    consumeSpace amount { state with clock := clock } =
      (consumeSpace amount state).map (fun next => { next with clock := clock }) := by
  simp only [consumeSpace]
  split <;> simp_all

/-- Replacing every field but the clock with its own value is the clock update. -/
theorem state_update_clock_only {C F : Type} (state : State C F) (clock : Nat) :
    { state with
      stack := state.stack
      localsSize := state.localsSize
      stackMax := state.stackMax
      peakHeapLength := state.peakHeapLength
      locals := state.locals
      space := state.space
      handler := state.handler
      clock := clock
      stackFrameSizes := state.stackFrameSizes
      compile := state.compile } = { state with clock := clock } := rfl

/-- Exact HOL `space_consumed_with_clock` (`dataPropsScript.sml:1861`): the
space requirement of an operation does not depend on the clock. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "space_consumed_with_clock"]
theorem spaceConsumed_clock {C F : Type} (state : State C F) (op : ClosLang.Op)
    (values : List DataSem.Value) (clock : Nat) :
    spaceConsumed { state with clock := clock } op values = spaceConsumed state op values :=
  rfl

/-- The space stage reads the heap fields and preserves the clock. -/
theorem doSpace_clock {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (clock : Nat) :
    doSpace op values { state with clock := clock } =
      (doSpace op values state).map (fun next => { next with clock := clock }) := by
  by_cases reset : DataLang.opSpaceReset op
  · simp only [doSpace, reset, sizeOfHeapArgs_with_clock, spaceConsumed_clock]
    rfl
  · by_cases req : DataSpace.opSpaceReq op values.length = 0
    · simp only [doSpace, reset, req]
      rfl
    · simp only [doSpace, reset, req, consumeSpace_clock]
      rfl

/-- Stack accounting is a record update of non-clock fields. -/
theorem doStack_clock_update {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (clock : Nat) :
    doStack op values { state with clock := clock } =
      { doStack op values state with clock := clock } := by
  simp [doStack]

/-- The limit check is a record update of non-clock fields. -/
theorem doLimSafe_clock_update {C F : Type} (state : State C F) (op : ClosLang.Op)
    (values : List DataSem.Value) (clock : Nat) :
    doLimSafe { state with clock := clock } op values =
      { doLimSafe state op values with clock := clock } := by
  simp [doLimSafe]

/-- The auxiliary dispatcher commutes with a clock update: the field frame shows
that it leaves every field it does not read unchanged. -/
theorem doAppAux_clock {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (clock : Nat) :
    doAppAux op values { state with clock := clock } =
      mapResult (fun (value, next) => (value, { next with clock := clock })) id
        (doAppAux op values state) := by
  have key := doAppAux_withFields op values state state.stack state.localsSize state.stackMax
    state.peakHeapLength state.locals state.space state.handler clock state.stackFrameSizes
    state.compile
  rw [state_update_clock_only] at key
  cases run : doAppAux op values state with
  | err error => simpa [run, mapResult, mapErrorResult_id] using key
  | val pair =>
    obtain ⟨value, next⟩ := pair
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
      doAppAux_fieldFrame op values state next value run
    simpa [run, mapResult, mapErrorResult_id, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10]
      using key

/-- Installation reads the oracle, code and compile callback, so it commutes
with a clock update. -/
theorem doInstall_clock {C F R : Type} (args : List DataSem.Value) (state : State C F)
    (clock : Nat) :
    doInstall args { state with clock := clock } =
      mapResult (fun ((value, next) : DataSem.Value × State C F) =>
          (value, { next with clock := clock })) (id : R → R)
        (doInstall args state) := by
  simp only [doInstall, mapResult, mapErrorResult]
  repeat' (split <;> try rfl)

/-- The dispatcher's non-install branch: space, stack, limit and auxiliary
application in their original order. -/
noncomputable def doAppOther {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) : Result (DataSem.Value × State C F) DataSem.Value :=
  match doSpace op values state with
  | none => .err (.abort .typeError)
  | some next => doAppAux op values (doStack op values (doLimSafe next op values))

/-- The non-install branch commutes with a clock update. -/
theorem doAppOther_clock {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (clock : Nat) :
    doAppOther op values { state with clock := clock } =
      mapResult (fun (value, next) => (value, { next with clock := clock })) id
        (doAppOther op values state) := by
  simp only [doAppOther, doSpace_clock]
  cases h : doSpace op values state with
  | none => simp [mapResult, mapErrorResult_id]
  | some next =>
    simp only [Option.map_some]
    rw [doLimSafe_clock_update, doStack_clock_update, doAppAux_clock]

/-- Exact HOL `do_app_with_clock` (`dataPropsScript.sml:1869`): applying a
primitive at a replaced clock gives the original result with the clock replaced
in the resulting state. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_with_clock"]
theorem doApp_with_clock {C F : Type} (op : ClosLang.Op) (values : List DataSem.Value)
    (state : State C F) (clock : Nat) :
    doApp op values { state with clock := clock } =
      mapResult (fun (value, next) => (value, { next with clock := clock })) id
        (doApp op values state) := by
  cases op with
  | install =>
    simp only [doApp]
    exact doInstall_clock values { state with stackMax := none, stackFrameSizes := .ln } clock
  | intOp op' =>
    cases op' with
    | greater => simp [doApp, mapResult, mapErrorResult]
    | greaterEq => simp [doApp, mapResult, mapErrorResult]
    | const a => exact doAppOther_clock (.intOp (.const a)) values state clock
    | add => exact doAppOther_clock (.intOp .add) values state clock
    | sub => exact doAppOther_clock (.intOp .sub) values state clock
    | mult => exact doAppOther_clock (.intOp .mult) values state clock
    | div => exact doAppOther_clock (.intOp .div) values state clock
    | mod => exact doAppOther_clock (.intOp .mod) values state clock
    | less => exact doAppOther_clock (.intOp .less) values state clock
    | lessEq => exact doAppOther_clock (.intOp .lessEq) values state clock
    | lessConstSmall n => exact doAppOther_clock (.intOp (.lessConstSmall n)) values state clock
  | label label => exact doAppOther_clock (.label label) values state clock
  | ffi name => exact doAppOther_clock (.ffi name) values state clock
  | thunkOp op' => exact doAppOther_clock (.thunkOp op') values state clock
  | globOp op' => exact doAppOther_clock (.globOp op') values state clock
  | blockOp op' => exact doAppOther_clock (.blockOp op') values state clock
  | memOp op' => exact doAppOther_clock (.memOp op') values state clock
  | wordOp op' => exact doAppOther_clock (.wordOp op') values state clock

/-- Exact HOL `do_app_change_clock` (`dataPropsScript.sml:1893`): a successful
application keeps its result when only the clock is replaced. -/
@[hol "cakeml/compiler/backend/semantics/dataPropsScript.sml" "do_app_change_clock"]
theorem doApp_change_clock {C F : Type} (op : ClosLang.Op) (args : List DataSem.Value)
    (state : State C F) (res : DataSem.Value) (next : State C F) (clock : Nat)
    (run : doApp op args state = .val (res, next)) :
    doApp op args { state with clock := clock } = .val (res, { next with clock := clock }) := by
  rw [doApp_with_clock, run, mapResult]

end Flapjack.Compiler.Backend.DataProps

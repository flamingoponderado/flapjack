import Flapjack.Compiler.Backend.DataSpace.Proofs.Accounting
import Flapjack.Compiler.Backend.Semantics.DataSem.Apply

/-! Independence of primitive results from the reserved-space field. -/
namespace Flapjack.Compiler.Backend.DataSpace
open Flapjack Flapjack.Compiler.Backend.DataSem Flapjack.SemanticPrimitivesHOL

/-- Adjusting the reserved space on an auxiliary primitive result leaves its
value and all other state fields unchanged. This is auxiliary infrastructure. -/
def replaceResultSpace {C F : Type} (space : Nat) :
    Result (DataSem.Value × State C F) DataSem.Value → Result (DataSem.Value × State C F) DataSem.Value
  | .err error => .err error
  | .val (value, state) => .val (value, { state with space := space })

/-- Label lookup is independent of the reserved-space field. -/
theorem doAppAux_label_with_space {C F : Type} (label : Nat) (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.label label) values { state with space := space } =
      replaceResultSpace space (doAppAux (.label label) values state) := by
  cases values with
  | nil =>
    simp only [doAppAux, applyNonFfi]
    split <;> simp_all [replaceResultSpace]
  | cons first rest => simp [doAppAux, applyNonFfi, replaceResultSpace]

/-- Integer primitives are independent of reserved space. -/
theorem doAppAux_int_with_space {C F : Type} (op : ClosLang.IntOp) (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.intOp op) values { state with space := space } =
      replaceResultSpace space (doAppAux (.intOp op) values state) := by
  simp only [doAppAux, applyNonFfi]
  cases doIntApp op values <;> simp [replaceResultSpace]

/-- Word primitives are independent of reserved space. -/
theorem doAppAux_word_with_space {C F : Type} (op : ClosLang.WordOp) (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.wordOp op) values { state with space := space } =
      replaceResultSpace space (doAppAux (.wordOp op) values state) := by
  simp only [doAppAux, applyNonFfi]
  cases doWordApp op values <;> simp [replaceResultSpace]

/-- Global-pointer primitives are independent of reserved space. -/
theorem doAppAux_global_with_space {C F : Type} (op : ClosLang.GlobOp) (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.globOp op) values { state with space := space } =
      replaceResultSpace space (doAppAux (.globOp op) values state) := by
  cases op with
  | allocGlobal => simp [doAppAux, applyNonFfi, replaceResultSpace]
  | globalsPtr =>
    cases values with
    | cons first rest => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | nil => cases found : state.global <;> simp [doAppAux, applyNonFfi, replaceResultSpace, found]
  | setGlobalsPtr =>
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | nil => cases first <;> simp [doAppAux, applyNonFfi, replaceResultSpace]; case refPtr flag ptr => cases flag <;> simp
  | global index =>
    cases values with
    | cons first rest => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | nil =>
      cases foundGlobal : state.global with
      | none => simp [doAppAux, applyNonFfi, replaceResultSpace, foundGlobal]
      | some ptr =>
        cases found : sptLookup ptr state.refs with
        | none => simp [doAppAux, applyNonFfi, replaceResultSpace, foundGlobal, found]
        | some entry =>
          cases entry <;> simp [doAppAux, applyNonFfi, replaceResultSpace, foundGlobal, found]
          case valueArray values => cases values[index]? <;> simp [foundGlobal]
  | setGlobal index =>
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | nil =>
        cases foundGlobal : state.global with
        | none => simp [doAppAux, applyNonFfi, replaceResultSpace, foundGlobal]
        | some ptr =>
          cases found : sptLookup ptr state.refs with
          | none => simp [doAppAux, applyNonFfi, replaceResultSpace, foundGlobal, found]
          | some entry =>
            cases entry <;> simp [doAppAux, applyNonFfi, replaceResultSpace, foundGlobal, found]
            case valueArray values =>
              by_cases bound : index < values.length <;> simp [bound]

/-- Thunk allocation and updates do not inspect reserved space. -/
theorem doAppAux_thunk_with_space {C F : Type} (op : AstHOL.ThunkOp) (values : List DataSem.Value)
    (state : State C F) (space : Nat) :
    doAppAux (.thunkOp op) values { state with space := space } =
      replaceResultSpace space (doAppAux (.thunkOp op) values state) := by
  cases op with
  | forceThunk => cases values <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
  | allocThunk mode =>
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | cons second tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | nil =>
        by_cases bad : badThunkUpdate mode first state.refs <;> simp [doAppAux, applyNonFfi, replaceResultSpace, bad]
  | updateThunk mode =>
    cases values with
    | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
    | cons first rest =>
      cases rest with
      | nil => simp [doAppAux, applyNonFfi, replaceResultSpace]
      | cons second tail =>
        cases tail with
        | cons third tail => simp [doAppAux, applyNonFfi, replaceResultSpace]
        | nil =>
          cases first <;> simp [doAppAux, applyNonFfi, replaceResultSpace]
          case refPtr flag ptr =>
            cases flag with
            | true => simp
            | false =>
              by_cases bad : badThunkUpdate mode second state.refs
              · simp [bad]
              · cases found : sptLookup ptr state.refs with
                | none => simp [bad, found]
                | some entry =>
                  cases entry <;> simp [bad, found]
                  case thunk oldMode oldValue => cases oldMode <;> simp

end Flapjack.Compiler.Backend.DataSpace

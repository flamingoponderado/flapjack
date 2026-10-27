import Flapjack.Compiler.Backend.Semantics.FlatSem

/-! Thunk inspection and update helpers in the flat evaluator. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- The three original outcomes of inspecting a thunk reference. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "dest_thunk_ret"]
inductive DestThunkResult where
  | badRef
  | notThunk
  | isThunk : ThunkMode → Value → DestThunkResult

/-- Inspect a singleton location, retaining the reference-flag check. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "dest_thunk_def"]
def destThunk (values : List Value) (store : Store Value) : DestThunkResult :=
  match values with
  | [.loc isRef index] => match storeLookup index store with
    | none => .badRef
    | some (.thunk mode value) => if isRef then .badRef else .isThunk mode value
    | some _ => .notThunk
  | _ => .notThunk

/-- Update an unevaluated thunk when the replacement is not itself a thunk. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "update_thunk_def"]
def updateThunk (targets : List Value) (store : Store Value) (values : List Value) : Option (Store Value) :=
  match targets, values with
  | [.loc false index], [value] => match destThunk [value] store with
    | .notThunk => storeAssign index (.thunk .evaluated value) store
    | _ => none
  | _, _ => none

/-- An evaluated thunk must not contain another thunk or an invalid reference. -/
@[hol "cakeml/compiler/backend/semantics/flatSemScript.sml" "bad_thunk_update_def"]
def badThunkUpdate (mode : ThunkMode) (value : Value) (store : Store Value) : Bool :=
  if mode = .evaluated then
    match destThunk [value] store with
    | .notThunk => false
    | _ => true
  else false

end Flapjack.Compiler.Backend.FlatSem

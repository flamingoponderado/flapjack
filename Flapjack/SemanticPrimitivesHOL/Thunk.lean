import Flapjack.SemanticPrimitivesHOL

/-! Source thunk and byte-XOR operations. Statement review is pending. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "exp_or_val"]
inductive ExpOrVal where
  | exp : AstHOL.Exp → ExpOrVal
  | val : Value → ExpOrVal

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "store_ffi"]
abbrev StoreFfi (α σ : Type) := Store α × HolFfiState σ

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "xor_bytes_def"]
def xorBytes : List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))
  | [], ys => some ys
  | _ :: _, [] => none
  | x :: xs, y :: ys => (xorBytes xs ys).map ((x ^^^ y) :: ·)

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "dest_thunk_ret"]
inductive DestThunkResult where
  | badRef
  | notThunk
  | isThunk : ThunkMode → Value → DestThunkResult

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "dest_thunk_def"]
def destThunk (values : List Value) (store : Store Value) : DestThunkResult :=
  match values with
  | [.loc isRef index] => match storeLookup index store with
    | none => .badRef
    | some (.thunk mode value) => if isRef then .badRef else .isThunk mode value
    | some _ => .notThunk
  | _ => .notThunk

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "update_thunk_def"]
def updateThunk (targets : List Value) (store : Store Value) (values : List Value) : Option (Store Value) :=
  match targets, values with
  | [.loc false index], [value] => match destThunk [value] store with
    | .notThunk => storeAssign index (.thunk .evaluated value) store
    | _ => none
  | _, _ => none

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "bad_thunk_update_def"]
def badThunkUpdate (mode : ThunkMode) (value : Value) (store : Store Value) : Bool :=
  if mode = .evaluated then
    match destThunk [value] store with
    | .notThunk => false
    | _ => true
  else false

@[hol "cakeml/semantics/semanticPrimitivesScript.sml" "thunk_op_def"]
def thunkOp {σ β : Type} (state : StoreFfi Value σ) (op : ThunkOp) (values : List Value) :
    Option (StoreFfi Value σ × Result Value β) :=
  let (store, ffi) := state
  match op, values with
  | .allocThunk mode, [value] =>
    if badThunkUpdate mode value store then none else
      let (store', index) := storeAlloc (.thunk mode value) store
      some ((store', ffi), .val (.loc false index))
  | .updateThunk mode, [.loc false index, value] =>
    if badThunkUpdate mode value store then none else
      (storeAssign index (.thunk mode value) store).map fun store' =>
        ((store', ffi), .val (.conv none []))
  | _, _ => none

end Flapjack.SemanticPrimitivesHOL

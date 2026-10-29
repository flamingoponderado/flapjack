import Flapjack.Compiler.Backend.Semantics.ClosSem.State

/-! Thunk inspection and updates in the closure semantics. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.AstHOL

/-- Result of examining a possible thunk pointer. -/
inductive DestThunkResult where
  | badRef
  | notThunk
  | isThunk : ThunkMode → Value → DestThunkResult

/-- Inspect a singleton pointer, including the invalid-reference flag. The
finite-map representation remains pending HOL correspondence review. -/
def destThunk (values : List Value) (refs : HolFiniteMapExact Nat (Ref Value)) : DestThunkResult :=
  match values with
  | [.refPtr isRef index] => match refs.lookup index with
    | none => .badRef
    | some (.thunk mode value) => if isRef then .badRef else .isThunk mode value
    | some _ => .notThunk
  | _ => .notThunk

/-- Update a thunk only if its previous mode is unevaluated. -/
def storeThunk (index : Nat) (value : Ref Value) (refs : HolFiniteMapExact Nat (Ref Value)) :
    Option (HolFiniteMapExact Nat (Ref Value)) :=
  match refs.lookup index with
  | some (.thunk .notEvaluated _) => some (refs.updateEq (index, value))
  | _ => none

/-- An evaluated thunk cannot be updated to a thunk or invalid reference. -/
def updateThunk (targets : List Value) (refs : HolFiniteMapExact Nat (Ref Value))
    (values : List Value) : Option (HolFiniteMapExact Nat (Ref Value)) :=
  match targets, values with
  | [.refPtr false index], [value] => match destThunk [value] refs with
    | .notThunk => storeThunk index (.thunk .evaluated value) refs
    | _ => none
  | _, _ => none

/-- Test the original restriction on evaluated thunk contents. -/
def badThunkUpdate (mode : ThunkMode) (value : Value) (refs : HolFiniteMapExact Nat (Ref Value)) : Bool :=
  if mode = .evaluated then
    match destThunk [value] refs with
    | .notThunk => false
    | _ => true
  else false

end Flapjack.Compiler.Backend.ClosSem

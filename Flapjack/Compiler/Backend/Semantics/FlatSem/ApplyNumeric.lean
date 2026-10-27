import Flapjack.Compiler.Backend.Semantics.FlatSem.Test
import Flapjack.SemanticPrimitivesHOL.ApplyNumeric

/-! Numeric cases of flat primitive application. The reused source numeric
dispatcher and the assembled flat dispatcher remain subject to source review. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Run the shared source numeric operation on flat projections and map its
result back to the flat carrier. -/
noncomputable def applyNumericProjection {C F : Type} (state : State C F) (op : Op)
    (values : List Value) (errorValue : Value) : Option (State C F × Result Value Value) := do
  let (_, result) ← SemanticPrimitivesHOL.doApp ([], state.ffi) op (values.map flatToValue)
  match result with
  | .val value => some (state, .val (valueToFlat value))
  | .err (.raise _) => some (state, .err (.raise errorValue))
  | .err (.abort error) => some (state, .err (.abort error))

/-- Numeric, equality and test cases. Outer `none` denotes an operation outside
this dispatcher; `some none` is the original primitive's failure. The source
numeric dispatcher retains its floating-point model assumptions. -/
noncomputable def doAppNumeric {C F : Type} (state : State C F) (op : Op) (values : List Value) :
    Option (Option (State C F × Result Value Value)) :=
  match op with
  | .shift _ _ _ => some (applyNumericProjection state op values divExnV)
  | .arith _ _ => some (applyNumericProjection state op values divExnV)
  | .fromTo _ _ => some (applyNumericProjection state op values chrExnV)
  | .equality => some <| match values with
    | [first, second] => match doEq first second with
      | .typeError => none
      | .val result => some (state, .val (boolValue result))
    | _ => none
  | .test test typ => some <| match values with
    | [first, second] => match doTest test typ first second with
      | .typeError => none
      | .val result => some (state, .val (boolValue result))
    | _ => none
  | _ => none

end Flapjack.Compiler.Backend.FlatSem

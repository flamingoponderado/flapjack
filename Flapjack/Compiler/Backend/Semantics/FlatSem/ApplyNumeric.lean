module

public import Flapjack.Compiler.Backend.Semantics.FlatSem.Test
public import Flapjack.SemanticPrimitivesHOL.ApplyNumeric
public import Flapjack.SemanticPrimitivesProps.Shift

@[expose] public section

/-! Numeric cases of flat primitive application. The reused source dispatcher
has its own pending whole-definition review; flat case equations are in the
`Apply*Source` submodules. -/
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
  | .shift width shift amount => some <| match values with
    | [.litv lit] => match Flapjack.SemanticPrimitivesProps.doShift shift amount width lit with
      | some result => some (state, .val (.litv result))
      | none => none
    | _ => none
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

/-- The direct flat shift agrees with the former source-primitive projection on
every argument list. This correspondence is Flapjack infrastructure. -/
theorem shift_projection_eq {C F : Type} (state : State C F) (width : WordSize)
    (shift : Shift) (amount : Nat) (values : List Value) :
    (match values with
     | [.litv lit] => match Flapjack.SemanticPrimitivesProps.doShift shift amount width lit with
       | some result => some (state, .val (.litv result))
       | none => none
     | _ => none) =
      applyNumericProjection state (.shift width shift amount) values divExnV := by
  cases width <;> cases values with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil =>
      cases x <;> simp [applyNumericProjection, SemanticPrimitivesHOL.doApp,
        doAppNumericCore, doAppBasic, flatToValue, valueToFlat,
        Flapjack.SemanticPrimitivesProps.doShift,
        Flapjack.SemanticPrimitivesProps.shiftLookup, shift8Lookup, shift64Lookup]
      all_goals repeat' first | split at * | simp_all [SemanticPrimitivesHOL.boolValue]
    | cons y ys =>
      cases x <;> simp [applyNumericProjection, SemanticPrimitivesHOL.doApp,
        doAppNumericCore, doAppBasic, flatToValue]

end Flapjack.Compiler.Backend.FlatSem

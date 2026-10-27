import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyMemory
import Flapjack.Compiler.Backend.Semantics.FlatSem.Conversions
import Flapjack.Compiler.Backend.Semantics.FlatSem.Thunk

/-! Flat source-operation cases for strings, lists, vectors and thunks. The
complete primitive dispatcher is not yet assembled. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- The data-operation cases of flat primitive application. Outer `none`
means the operation is outside this dispatcher; `some none` means the original
operation failed. This is not the complete HOL `do_app`. -/
def doAppData {C F : Type} (state : State C F) (op : Op) (values : List Value) :
    Option (Option (State C F × Result Value Value)) :=
  match op with
  | .implode => some do
    match values with
    | [value] => some (state, .val (.litv (.strLit (.implode (← valueToCharList value)))))
    | _ => none
  | .explode => some <| match values with
    | [.litv (.strLit str)] => some (state, .val (listToValue (str.explode.map (.litv ∘ Lit.char))))
    | _ => none
  | .strsub => some <| match values with
    | [.litv (.strLit str), .litv (.intLit index)] => readIndexed state false str.explode index (.litv ∘ Lit.char)
    | _ => none
  | .strlen => some <| match values with
    | [.litv (.strLit str)] => some (state, .val (.litv (.intLit str.explode.length)))
    | _ => none
  | .strcat => some do
    match values with
    | [value] =>
      let parts ← valueToList value
      let result ← valuesToString parts
      some (state, .val (.litv (.strLit result)))
    | _ => none
  | .vfromList => some do
    match values with
    | [value] => some (state, .val (.vectorv (← valueToList value)))
    | _ => none
  | .vsub | .vsubUnsafe => some <| match values with
    | [.vectorv items, .litv (.intLit index)] => readIndexed state (op == .vsubUnsafe) items index id
    | _ => none
  | .vlength => some <| match values with
    | [.vectorv items] => some (state, .val (.litv (.intLit items.length)))
    | _ => none
  | .listAppend => some do
    match values with
    | [first, second] =>
      let left ← valueToList first
      let right ← valueToList second
      some (state, .val (listToValue (left ++ right)))
    | _ => none
  | .configGC => some <| match values with
    | [.litv (.intLit _), .litv (.intLit _)] => some (state, .val unitValue)
    | _ => none
  | .thunkOp thunk => some <| match thunk, values with
    | .allocThunk mode, [value] =>
      if badThunkUpdate mode value state.refs then none else
      let (refs, address) := storeAlloc (.thunk mode value) state.refs
      some ({ state with refs := refs }, .val (.loc false address))
    | .updateThunk mode, [.loc false address, value] => do
      if badThunkUpdate mode value state.refs then none else
      let refs ← storeAssign address (.thunk mode value) state.refs
      some ({ state with refs := refs }, .val unitValue)
    | _, _ => none
  | .ffi name => some do
    match values with
    | [.litv (.strLit configuration), .loc _ address] =>
      match storeLookup address state.refs with
      | some (.w8array bytes) =>
        match callFFIHOL state.ffi (.extCall name) configuration.explode bytes with
        | .ret ffi result =>
          let refs ← storeAssign address (.w8array result) state.refs
          some ({ state with refs := refs, ffi := ffi }, .val unitValue)
        | .final event => some (state, .err (.abort (.ffiError event)))
      | _ => none
    | _ => none
  | _ => none

end Flapjack.Compiler.Backend.FlatSem

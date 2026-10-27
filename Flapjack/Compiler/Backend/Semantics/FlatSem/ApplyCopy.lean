import Flapjack.Compiler.Backend.Semantics.FlatSem.ApplyMemory
import Flapjack.SemanticPrimitivesHOL.Array
import Flapjack.SemanticPrimitivesHOL.Thunk

/-! Flat string and byte-array copy operations. This is part of the original
primitive dispatcher, which has not yet been assembled or reviewed in full. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Copy and XOR cases of flat primitive application. Outer `none` denotes
an operation outside this dispatcher; `some none` denotes primitive failure. -/
def doAppCopy {C F : Type} (state : State C F) (op : Op) (values : List Value) :
    Option (Option (State C F × Result Value Value)) :=
  match op with
  | .copyStrStr => some <| match values with
    | [.litv (.strLit str), .litv (.intLit offset), .litv (.intLit length)] =>
      match copyArray (str.explode, offset) length none with
      | none => boundsFailure state false
      | some chars => some (state, .val (.litv (.strLit (.implode chars))))
    | _ => none
  | .copyStrAw8 => some do
    match values with
    | [.litv (.strLit str), .litv (.intLit offset), .litv (.intLit length),
        .loc _ destination, .litv (.intLit dstOffset)] =>
      match storeLookup destination state.refs with
      | some (.w8array bytes) => match copyArray (str.explode, offset) length (some (bytes, dstOffset)) with
        | none => boundsFailure state false
        | some result =>
          let refs ← storeAssign destination (.w8array result) state.refs
          some ({ state with refs := refs }, .val unitValue)
      | _ => none
    | _ => none
  | .copyAw8Str => some <| match values with
    | [.loc _ source, .litv (.intLit offset), .litv (.intLit length)] =>
      match storeLookup source state.refs with
      | some (.w8array bytes) => match copyArray (bytes, offset) length none with
        | none => boundsFailure state false
        | some result => some (state, .val (.litv (.strLit (.implode result))))
      | _ => none
    | _ => none
  | .copyAw8Aw8 => some do
    match values with
    | [.loc _ source, .litv (.intLit offset), .litv (.intLit length),
        .loc _ destination, .litv (.intLit dstOffset)] =>
      match storeLookup source state.refs, storeLookup destination state.refs with
      | some (.w8array bytes), some (.w8array dst) =>
        match copyArray (bytes, offset) length (some (dst, dstOffset)) with
        | none => boundsFailure state false
        | some result =>
          let refs ← storeAssign destination (.w8array result) state.refs
          some ({ state with refs := refs }, .val unitValue)
      | _, _ => none
    | _ => none
  | .xorAw8StrUnsafe => some do
    match values with
    | [.loc _ destination, .litv (.strLit str)] =>
      match storeLookup destination state.refs with
      | some (.w8array bytes) =>
        let result ← xorBytes str.explode bytes
        let refs ← storeAssign destination (.w8array result) state.refs
        some ({ state with refs := refs }, .val unitValue)
      | _ => none
    | _ => none
  | _ => none

end Flapjack.Compiler.Backend.FlatSem

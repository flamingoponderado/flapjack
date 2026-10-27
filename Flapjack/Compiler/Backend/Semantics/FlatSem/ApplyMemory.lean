import Flapjack.Compiler.Backend.Semantics.FlatSem.Primitives

/-! Flat primitive application for references and arrays. The complete
`do_app` also includes non-memory cases and is not yet assembled. -/
namespace Flapjack.Compiler.Backend.FlatSem
open Flapjack.AstHOL Flapjack.SemanticPrimitivesHOL

/-- Bounds-error helper for the partial memory dispatcher. -/
def boundsFailure {C F : Type} (state : State C F) (unsafeOp : Bool) :
    Option (State C F × Result Value Value) :=
  if unsafeOp then none else some (state, .err (.raise subscriptExnV))

/-- Shared indexed-read helper for the partial memory dispatcher. -/
def readIndexed {C F α : Type} (state : State C F) (unsafeOp : Bool)
    (items : List α) (index : Int) (toValue : α → Value) : Option (State C F × Result Value Value) :=
  if index < 0 then boundsFailure state unsafeOp else
  match items[index.toNat]? with
  | none => boundsFailure state unsafeOp
  | some value => some (state, .val (toValue value))

private def updateIndexed {C F α : Type} (state : State C F) (unsafeOp : Bool)
    (address : Nat) (items : List α) (index : Int) (value : α)
    (asStore : List α → StoreValue Value) : Option (State C F × Result Value Value) := do
  if index < 0 || items.length ≤ index.toNat then boundsFailure state unsafeOp else
  let refs ← storeAssign address (asStore (items.set index.toNat value)) state.refs
  some ({ state with refs := refs }, .val unitValue)

/-- Reference and array cases of flat primitive application. An outer `none`
marks an operation outside this partial dispatcher; `some none` is the
original type-error or unsafe-bounds result for a supported operation. This is
not tagged as the complete HOL `do_app`. -/
def doAppMemory {C F : Type} (state : State C F) (op : Op) (values : List Value) :
    Option (Option (State C F × Result Value Value)) :=
  match op with
  | .opassign => some do
    match values with
    | [.loc _ address, value] =>
      let refs ← storeAssign address (.refv value) state.refs
      some ({ state with refs := refs }, .val unitValue)
    | _ => none
  | .opref => some <| match values with
    | [value] =>
      let (refs, address) := storeAlloc (.refv value) state.refs
      some ({ state with refs := refs }, .val (.loc true address))
    | _ => none
  | .aw8alloc => some <| match values with
    | [.litv (.intLit size), .litv (.word8 value)] =>
      if size < 0 then boundsFailure state false else
      let (refs, address) := storeAlloc (.w8array (List.replicate size.toNat value)) state.refs
      some ({ state with refs := refs }, .val (.loc true address))
    | _ => none
  | .aw8sub | .aw8subUnsafe => some <| match values with
    | [.loc _ address, .litv (.intLit index)] => match storeLookup address state.refs with
      | some (.w8array bytes) => readIndexed state (op == .aw8subUnsafe) bytes index (.litv ∘ Lit.word8)
      | _ => none
    | _ => none
  | .aw8length => some <| match values with
    | [.loc _ address] => match storeLookup address state.refs with
      | some (.w8array bytes) => some (state, .val (.litv (.intLit bytes.length)))
      | _ => none
    | _ => none
  | .aw8update | .aw8updateUnsafe => some <| match values with
    | [.loc _ address, .litv (.intLit index), .litv (.word8 value)] => match storeLookup address state.refs with
      | some (.w8array bytes) => updateIndexed state (op == .aw8updateUnsafe) address bytes index value .w8array
      | _ => none
    | _ => none
  | .aalloc => some <| match values with
    | [.litv (.intLit size), value] =>
      if size < 0 then boundsFailure state false else
      let (refs, address) := storeAlloc (.varray (List.replicate size.toNat value)) state.refs
      some ({ state with refs := refs }, .val (.loc true address))
    | _ => none
  | .aallocFixed =>
    let (refs, address) := storeAlloc (.varray values) state.refs
    some (some ({ state with refs := refs }, .val (.loc true address)))
  | .asub | .asubUnsafe => some <| match values with
    | [.loc _ address, .litv (.intLit index)] => match storeLookup address state.refs with
      | some (.varray items) => readIndexed state (op == .asubUnsafe) items index id
      | _ => none
    | _ => none
  | .alength => some <| match values with
    | [.loc _ address] => match storeLookup address state.refs with
      | some (.varray items) => some (state, .val (.litv (.intLit items.length)))
      | _ => none
    | _ => none
  | .aupdate | .aupdateUnsafe => some <| match values with
    | [.loc _ address, .litv (.intLit index), value] => match storeLookup address state.refs with
      | some (.varray items) => updateIndexed state (op == .aupdateUnsafe) address items index value .varray
      | _ => none
    | _ => none
  | _ => none

end Flapjack.Compiler.Backend.FlatSem

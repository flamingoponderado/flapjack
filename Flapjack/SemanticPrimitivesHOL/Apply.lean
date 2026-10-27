import Flapjack.SemanticPrimitivesHOL.Primitives
import Flapjack.SemanticPrimitivesHOL.Conversions
import Flapjack.SemanticPrimitivesHOL.Operations

/-! Initial source primitive application cases. This is Flapjack infrastructure
for assembling the source evaluator, not a port of the complete HOL `do_app`:
outer `none` means an operation is not implemented, while `some none` means
HOL's type-error result for a supported operation. -/
namespace Flapjack.SemanticPrimitivesHOL
open Flapjack.AstHOL

abbrev BasicAppResult (σ : Type) :=
  (Store Value × HolFfiState σ) × Result Value Value

private def boundsFailure {σ : Type} (state : Store Value × HolFfiState σ)
    (isUnsafe : Bool) : Option (BasicAppResult σ) :=
  if isUnsafe then none else some (state, .err (.raise subExnV))

private def readIndexed {σ α : Type} (state : Store Value × HolFfiState σ)
    (isUnsafe : Bool) (items : List α) (index : Int) (toValue : α → Value) : Option (BasicAppResult σ) :=
  if index < 0 then boundsFailure state isUnsafe else
  match items[index.toNat]? with
  | none => boundsFailure state isUnsafe
  | some value => some (state, .val (toValue value))

private def updateIndexed {σ α : Type} (state : Store Value × HolFfiState σ)
    (isUnsafe : Bool) (address : Nat) (items : List α) (index : Int) (value : α)
    (asStore : List α → StoreValue Value) : Option (BasicAppResult σ) := do
  if index < 0 || items.length ≤ index.toNat then boundsFailure state isUnsafe else
  let store ← storeAssign address (asStore (items.set index.toNat value)) state.1
  some ((store, state.2), .val (.conv none []))

/-- Supported pure, reference, array, vector and list cases of source primitive application.
The complete HOL `do_app` has additional cases and no outer unsupported result;
this partial dispatcher therefore intentionally has no `@[hol]` attribute. -/
def doAppBasic {σ : Type} (state : Store Value × HolFfiState σ) (op : Op)
    (values : List Value) : Option (Option (BasicAppResult σ)) :=
  let (store, ffi) := state
  match op with
  | .listAppend => some do
    match values with
    | [first, second] =>
      let left ← valueToList first
      let right ← valueToList second
      some (state, .val (listToValue (left ++ right)))
    | _ => none
  | .shift .w8 shift amount => some <| match values with
    | [.litv (.word8 word)] => some (state, .val (.litv (.word8 (shift8Lookup shift word amount))))
    | _ => none
  | .shift .w64 shift amount => some <| match values with
    | [.litv (.word64 word)] => some (state, .val (.litv (.word64 (shift64Lookup shift word amount))))
    | _ => none
  | .equality => some <| match values with
    | [first, second] => match doEq first second with
      | .typeError => none
      | .val b => some (state, .val (boolValue b))
    | _ => none
  | .opassign => some do
    match values with
    | [.loc _ address, value] =>
      let store ← storeAssign address (.refv value) store
      some ((store, ffi), .val (.conv none []))
    | _ => none
  | .opref => some <| match values with
    | [value] =>
      let (store, address) := storeAlloc (.refv value) store
      some ((store, ffi), .val (.loc true address))
    | _ => none
  | .opderef => some <| match values with
    | [.loc _ address] => match storeLookup address store with
      | some (.refv value) => some (state, .val value)
      | _ => none
    | _ => none
  | .aw8alloc => some <| match values with
    | [.litv (.intLit size), .litv (.word8 value)] =>
      if size < 0 then boundsFailure state false else
      let (store, address) := storeAlloc (.w8array (List.replicate size.toNat value)) store
      some ((store, ffi), .val (.loc true address))
    | _ => none
  | .aw8sub | .aw8subUnsafe => some <| match values with
    | [.loc _ address, .litv (.intLit index)] => match storeLookup address store with
      | some (.w8array items) => readIndexed state (op == .aw8subUnsafe) items index (.litv ∘ Lit.word8)
      | _ => none
    | _ => none
  | .aw8length => some <| match values with
    | [.loc _ address] => match storeLookup address store with
      | some (.w8array items) => some (state, .val (.litv (.intLit items.length)))
      | _ => none
    | _ => none
  | .aw8update | .aw8updateUnsafe => some <| match values with
    | [.loc _ address, .litv (.intLit index), .litv (.word8 value)] => match storeLookup address store with
      | some (.w8array items) => updateIndexed state (op == .aw8updateUnsafe) address items index value .w8array
      | _ => none
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
  | .aalloc => some <| match values with
    | [.litv (.intLit size), value] =>
      if size < 0 then boundsFailure state false else
      let (store, address) := storeAlloc (.varray (List.replicate size.toNat value)) store
      some ((store, ffi), .val (.loc true address))
    | _ => none
  | .aallocEmpty => some <| match values with
    | [.conv none []] =>
      let (store, address) := storeAlloc (.varray []) store
      some ((store, ffi), .val (.loc true address))
    | _ => none
  | .aallocFixed =>
      let (store, address) := storeAlloc (.varray values) store
      some (some ((store, ffi), .val (.loc true address)))
  | .asub | .asubUnsafe => some <| match values with
    | [.loc _ address, .litv (.intLit index)] => match storeLookup address store with
      | some (.varray items) => readIndexed state (op == .asubUnsafe) items index id
      | _ => none
    | _ => none
  | .alength => some <| match values with
    | [.loc _ address] => match storeLookup address store with
      | some (.varray items) => some (state, .val (.litv (.intLit items.length)))
      | _ => none
    | _ => none
  | .aupdate | .aupdateUnsafe => some <| match values with
    | [.loc _ address, .litv (.intLit index), value] => match storeLookup address store with
      | some (.varray items) => updateIndexed state (op == .aupdateUnsafe) address items index value .varray
      | _ => none
    | _ => none
  | _ => none

end Flapjack.SemanticPrimitivesHOL

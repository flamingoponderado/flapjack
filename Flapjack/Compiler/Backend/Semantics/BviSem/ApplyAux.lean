import Flapjack.Compiler.Backend.Semantics.BviSem.Finalise
import Flapjack.Compiler.Backend.Semantics.BvlSem.Build
import Flapjack.Compiler.Backend.Semantics.ClosSem.Word
import Flapjack.Compiler.Backend.BackendCommon.SmallInt

/-! Source-shaped BVI-specific primitive dispatch. -/
namespace Flapjack.Compiler.Backend.BviSem
open Flapjack.Compiler.Backend.BvlSem
open Flapjack.Compiler.Backend.BackendCommon

/-- BVI-specific primitive handling. `none` denotes a type error, `some none`
delegates to BVL, and `some (some ...)` returns a value and state. This follows
`do_app_aux_def` but remains untagged while the recursive `finaliseCons` map
input/output correspondence is not qualified. -/
noncomputable def doAppAux {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s : BviState C F) : Option (Option (Value × BviState C F)) :=
  let result (value : Value) := some (some (value, s))
  let write (ptr : Nat) (entry : Ref Value) :=
    some (some (unitValue, { s with refs := s.refs.updateEq (ptr, entry) }))
  match op, args with
  | .intOp (.const n), [] => if smallEnoughInt n then result (.number n) else none
  | .intOp (.const _), _ => none
  | .label loc, [] => if (sptLookup loc s.code).isSome then result (.codePtr loc) else none
  | .label _, _ => none
  | .globOp .globalsPtr, [] => s.global.map (fun ptr => some (.refPtr true ptr, s))
  | .globOp .globalsPtr, _ => none
  | .globOp .setGlobalsPtr, [.refPtr true ptr] => some (some (unitValue, { s with global := some ptr }))
  | .globOp .setGlobalsPtr, _ => none
  | .globOp (.global index), [] => do
    let ptr ← s.global
    let .valueArray values ← s.refs.lookup ptr | none
    match values[index]? with
    | none => none
    | some value => result value
  | .globOp (.global _), _ => none
  | .globOp (.setGlobal index), [value] => do
    let ptr ← s.global
    let .valueArray values ← s.refs.lookup ptr | none
    if index < values.length then write ptr (.valueArray (values.set index value)) else none
  | .globOp (.setGlobal _), _ => none
  | .blockOp (.fromList tag), [length, list] => do
    let values ← valueToList list
    match length with
    | .number n => if n = Int.ofNat values.length then result (.block tag values) else none
    | _ => none
  | .blockOp (.fromList _), _ => none
  | .memOp (.refByte flag), [.number count, .number byte] => do
    if count < 0 then none else
      let byte ← Flapjack.Compiler.Backend.ClosSem.intToByte byte
      let ptr := leastUnusedRef s.refs
      some (some (.refPtr true ptr,
        { s with refs := s.refs.updateEq (ptr, .byteArray flag (List.replicate count.toNat byte)) }))
  | .memOp (.refByte _), _ => none
  | .memOp (.mutCons tag index), values =>
    match values[index]? with
    | none => none
    | some child =>
      let ptr := leastUnusedRef s.refs
      let entry := Ref.mutBlock tag false (values.take index) child (values.drop (index + 1))
      some (some (.refPtr false ptr, { s with refs := s.refs.updateEq (ptr, entry) }))
  | .memOp .updateCons, [.refPtr _ ptr, .number index, value] =>
    match s.refs.lookup ptr with
    | some (.mutBlock tag finalised left _ right) =>
      if index ≠ Int.ofNat left.length ∨ finalised then none
      else write ptr (.mutBlock tag false left value right)
    | _ => none
  | .memOp .finaliseCons, [value] =>
    (finaliseCons value s.refs).map (fun (resultValue, refs) => some (resultValue, { s with refs := refs }))
  | .globOp .allocGlobal, _ => none
  | .memOp .fromListByte, _ => none
  | .memOp .toListByte, _ => none
  | .memOp .concatByteVec, _ => none
  | .memOp (.copyByte true), _ => none
  | _, _ => some none

end Flapjack.Compiler.Backend.BviSem

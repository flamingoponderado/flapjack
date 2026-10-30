import Flapjack.Compiler.Backend.Semantics.BvlSem.ApplyBasic
import Flapjack.SemanticPrimitivesHOL.Array
import Flapjack.SemanticPrimitivesHOL.Compare

/-! Memory branches of the BVL primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString

/-- Decode a list of BVL numbers as bytes, rejecting values outside 0–255. -/
def byteNumbers : List Value → Option (List (BitVec 8))
  | [] => some []
  | .number number :: values => do
    let byte ← ClosSem.intToByte number
    let rest ← byteNumbers values
    pure (byte :: rest)
  | _ => none

private def byteArrays (refs : HolFiniteMapExact Nat (Ref Value)) : List Value → Option (List (List (BitVec 8)))
  | [] => some []
  | .refPtr true ptr :: values => do
    let .byteArray true bytes ← refs.lookup ptr | none
    let rest ← byteArrays refs values
    pure (bytes :: rest)
  | _ => none

/-- Source-shaped memory branches of BVL `do_app`. `none` denotes the source
type error. The full dispatcher, including installation and FFI, remains a
separate proof obligation. -/
noncomputable def applyMemory {C F : Type} (op : ClosLang.MemOp) (args : List Value) (s : State C F) :
    Option (Value × State C F) := by
  let result (value : Value) := some (value, s)
  let write (index : Nat) (value : Ref Value) :=
    some (unitValue, { s with refs := s.refs.updateEq (index, value) })
  let allocate (flag : Bool) (value : Ref Value) :=
    let index := leastUnusedRef s.refs
    some (Value.refPtr flag index, { s with refs := s.refs.updateEq (index, value) })
  exact match op, args with
  | .el, [.block _ values, .number index] =>
    if index < 0 then none else (values[index.toNat]?).bind result
  | .el, [.refPtr _ ptr, .number index] =>
    match s.refs.lookup ptr with
    | some (.valueArray values) => if index < 0 then none else (values[index.toNat]?).bind result
    | _ => none
  | .length, [.refPtr _ ptr] => match s.refs.lookup ptr with
    | some (.valueArray values) => result (.number values.length)
    | _ => none
  | .lengthByte, [.refPtr _ ptr] => match s.refs.lookup ptr with
    | some (.byteArray _ bytes) => result (.number bytes.length)
    | _ => none
  | .refByte false, [.number count, .number byte] => do
    if count < 0 then none else
      let b ← ClosSem.intToByte byte
      allocate true (.byteArray false (List.replicate count.toNat b))
  | .refArray, [.number count, value] =>
    if count < 0 then none else allocate true (.valueArray (List.replicate count.toNat value))
  | .ref, values => allocate true (.valueArray values)
  | .derefByte, [.refPtr _ ptr, .number index] => match s.refs.lookup ptr with
    | some (.byteArray _ bytes) =>
      if index < 0 then none else (bytes[index.toNat]?).bind (fun b => result (.number b.toNat))
    | _ => none
  | .updateByte, [.refPtr _ ptr, .number index, .number byte] => match s.refs.lookup ptr with
    | some (.byteArray flag bytes) => do
      if index < 0 ∨ index.toNat ≥ bytes.length then none else
        let b ← ClosSem.intToByte byte
        write ptr (.byteArray flag (bytes.set index.toNat b))
    | _ => none
  | .update, [.refPtr _ ptr, .number index, value] => match s.refs.lookup ptr with
    | some (.valueArray values) =>
      if index < 0 ∨ index.toNat ≥ values.length then none
      else write ptr (.valueArray (values.set index.toNat value))
    | _ => none
  | .concatByteVec, [value] => do
    let values ← valueToList value
    let chunks ← byteArrays s.refs values
    allocate true (.byteArray true chunks.flatten)
  | .fromListByte, [value] => do
    let values ← valueToList value
    let bytes ← byteNumbers values
    allocate true (.byteArray true bytes)
  | .toListByte, [.refPtr _ ptr] => match s.refs.lookup ptr with
    | some (.byteArray _ bytes) => result (listToValue (bytes.map (fun b => .number b.toNat)))
    | _ => none
  | .copyByte false, [.refPtr _ src, .number offset, .number length, .refPtr _ dst, .number dstOffset] => do
    let .byteArray _ source ← s.refs.lookup src | none
    let .byteArray flag bytes ← s.refs.lookup dst | none
    let copied ← copyArray (source, offset) length (some (bytes, dstOffset))
    write dst (.byteArray flag copied)
  | .copyByte true, [.refPtr _ src, .number offset, .number length] => do
    let .byteArray _ source ← s.refs.lookup src | none
    let copied ← copyArray (source, offset) length none
    allocate true (.byteArray true copied)
  | .xorByte, [.refPtr _ dst, .refPtr _ src] => do
    let .byteArray _ source ← s.refs.lookup src | none
    let .byteArray flag bytes ← s.refs.lookup dst | none
    let updated ← xorBytes source bytes
    write dst (.byteArray flag updated)
  | .stringCmp fast op, [.refPtr _ p, .refPtr _ q] => do
    let .byteArray _ a ← s.refs.lookup p | none
    let .byteArray _ b ← s.refs.lookup q | none
    result (boolValue (strCmp fast op (.implode a) (.implode b)))
  | .boundsCheckByte loose, [.refPtr _ ptr, .number index] => match s.refs.lookup ptr with
    | some (.byteArray _ bytes) =>
      result (boolValue (decide (0 ≤ index ∧ if loose then index ≤ Int.ofNat bytes.length else index < Int.ofNat bytes.length)))
    | _ => none
  | .boundsCheckArray, [.refPtr _ ptr, .number index] => match s.refs.lookup ptr with
    | some (.valueArray values) => result (boolValue (decide (0 ≤ index ∧ index < Int.ofNat values.length)))
    | _ => none
  | .configGC, [.number _, .number _] => result unitValue
  | _, _ => none

end Flapjack.Compiler.Backend.BvlSem

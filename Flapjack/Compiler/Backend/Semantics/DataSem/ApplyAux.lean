module

public import Flapjack.Compiler.Backend.Semantics.DataSem.Limits
public import Flapjack.Compiler.Backend.Semantics.DataSem.Finalise
public import Flapjack.Compiler.Backend.Semantics.DataSem.Build
public import Flapjack.Compiler.Backend.Semantics.DataSem.Equality
public import Flapjack.Compiler.Backend.Semantics.DataSem.Int
public import Flapjack.Compiler.Backend.Semantics.DataSem.Word
public import Flapjack.SemanticPrimitivesHOL.Array
public import Flapjack.SemanticPrimitivesHOL.Compare

@[expose] public section

/-! Primitive application in the data-language semantics. -/
namespace Flapjack.Compiler.Backend.DataSem
open Flapjack Flapjack.SemanticPrimitivesHOL Flapjack.Basis.Pure.MlString
open Classical

/-- Non-FFI branches of data-language primitive application. `none` denotes
an original type error; FFI is handled separately to retain final events. -/
noncomputable def applyNonFfi {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s : State C F) : Option (Value × State C F) := by
  let result (value : Value) := some (value, s)
  let write (ptr : Nat) (entry : BvlSem.Ref Value) :=
    some (unitValue, { s with refs := sptInsert ptr entry s.refs })
  let allocate (bit : Bool) (entry : BvlSem.Ref Value) :=
    let ptr := leastUnusedRef s.refs
    some (Value.refPtr bit ptr, { s with refs := sptInsert ptr entry s.refs })
  exact match op, args with
  | .label label, [] => if (sptLookup label s.code).isSome then result (.codePtr label) else none
  | .globOp .globalsPtr, [] => s.global.map (fun ptr => (.refPtr true ptr, s))
  | .globOp (.global index), [] => do
      let ptr ← s.global
      let .valueArray values ← sptLookup ptr s.refs | none
      let value ← values[index]?
      result value
  | .globOp (.setGlobal index), [value] => do
      let ptr ← s.global
      let .valueArray values ← sptLookup ptr s.refs | none
      if index < values.length then write ptr (.valueArray (values.set index value)) else none
  | .globOp .setGlobalsPtr, [.refPtr true ptr] => some (unitValue, { s with global := some ptr })
  | .blockOp (.fromList tag), [.number length, value] => do
      let values ← valueToList value
      if length = Int.ofNat values.length then
        if values.isEmpty then result (.block 0 tag []) else
          withFreshTimestamp s 1 (fun ts next => some (.block ts tag values, checkLim next values.length))
      else none
  | .memOp (.refByte flag), [.number count, .number byte] => do
      if count < 0 then none else
        let b ← ClosSem.intToByte byte
        allocate true (.byteArray flag (List.replicate count.toNat b))
  | .blockOp (.build parts), [] =>
      let (value, refs, stamps) := doBuildConst parts s.refs s.tstamps
      some (value, { s with refs := refs, tstamps := stamps })
  | .blockOp (.cons tag), values =>
      if values.isEmpty then result (.block 0 tag []) else
        withFreshTimestamp s 1 (fun ts next => some (.block ts tag values, checkLim next values.length))
  | .blockOp (.consExtend tag), .block _ _ previous :: .number lower :: .number length :: .number total :: values =>
      if lower < 0 ∨ length < 0 ∨ lower + length > Int.ofNat previous.length ∨
         total = 0 ∨ total ≠ Int.ofNat values.length + length then none else
        let values := values ++ (previous.drop lower.toNat).take length.toNat
        withFreshTimestamp s 1 (fun ts next => some (.block ts tag values, checkLim next values.length))
  | .memOp .el, [.block _ _ values, .number index] =>
      if index < 0 then none else (values[index.toNat]?).bind result
  | .memOp .el, [.refPtr _ ptr, .number index] => do
      let .valueArray values ← sptLookup ptr s.refs | none
      if index < 0 then none else (values[index.toNat]?).bind result
  | .blockOp (.elemAt index), [.block _ _ values] => (values[index]?).bind result
  | .blockOp (.elemAt index), [.refPtr _ ptr] => do
      let .valueArray values ← sptLookup ptr s.refs | none
      (values[index]?).bind result
  | .blockOp (.boolTest _), [a, b] => do
      let x ← destBool a
      let y ← destBool b
      result (boolValue (x == y))
  | .blockOp .boolNot, [value] => do
      let b ← destBool value
      result (boolValue (!b))
  | .blockOp .listAppend, [a, b] => do
      let values ← valueToList a
      let _ ← valueToList b
      withFreshTimestamp s values.length (fun ts next => some (listToValue ts b values, checkLim next 2))
  | .blockOp .lengthBlock, [.block _ _ values] => result (.number values.length)
  | .memOp .length, [.refPtr _ ptr] => do
      let .valueArray values ← sptLookup ptr s.refs | none
      result (.number values.length)
  | .memOp .lengthByte, [.refPtr _ ptr] => do
      let .byteArray _ bytes ← sptLookup ptr s.refs | none
      result (.number bytes.length)
  | .memOp .refArray, [.number count, value] =>
      if count < 0 then none else allocate true (.valueArray (List.replicate count.toNat value))
  | .memOp .derefByte, [.refPtr _ ptr, .number index] => do
      let .byteArray _ bytes ← sptLookup ptr s.refs | none
      if index < 0 then none else (bytes[index.toNat]?).bind (fun b => result (.number b.toNat))
  | .memOp .updateByte, [.refPtr _ ptr, .number index, .number byte] => do
      let .byteArray flag bytes ← sptLookup ptr s.refs | none
      if index < 0 ∨ index.toNat ≥ bytes.length then none else
        let b ← ClosSem.intToByte byte
        write ptr (.byteArray flag (bytes.set index.toNat b))
  | .memOp .xorByte, [.refPtr _ dst, .refPtr _ src] => do
      let .byteArray _ source ← sptLookup src s.refs | none
      let .byteArray flag bytes ← sptLookup dst s.refs | none
      let updated ← xorBytes source bytes
      write dst (.byteArray flag updated)
  | .memOp (.stringCmp fast cmp), [.refPtr _ a, .refPtr _ b] => do
      let .byteArray _ left ← sptLookup a s.refs | none
      let .byteArray _ right ← sptLookup b s.refs | none
      result (boolValue (strCmp fast cmp (.implode left) (.implode right)))
  | .memOp (.copyByte false), [.refPtr _ src, .number offset, .number length, .refPtr _ dst, .number dstOffset] => do
      let .byteArray _ source ← sptLookup src s.refs | none
      let .byteArray flag bytes ← sptLookup dst s.refs | none
      let copied ← copyArray (source, offset) length (some (bytes, dstOffset))
      write dst (.byteArray flag copied)
  | .blockOp (.tagEq tag), [.block _ found _] => result (boolValue (decide (found = tag)))
  | .blockOp (.lenEq length), [.block _ _ values] => result (boolValue (decide (values.length = length)))
  | .blockOp (.tagLenEq tag length), [.block _ found values] =>
      result (boolValue (decide (found = tag ∧ values.length = length)))
  | .blockOp (.equalConst (.int n)), [.number m] => result (boolValue (decide (n = m)))
  | .blockOp (.equalConst (.w64 a)), [.word64 b] => result (boolValue (decide (a = b)))
  | .blockOp (.equalConst (.str text)), [.refPtr _ ptr] => do
      let .byteArray true bytes ← sptLookup ptr s.refs | none
      result (boolValue (decide (bytes = text.explode)))
  | .blockOp .equal, [a, b] => match doEq s.refs a b with
      | .val value => result (boolValue value)
      | .typeError => none
  | .memOp .ref, values => allocate true (.valueArray values)
  | .memOp .update, [.refPtr _ ptr, .number index, value] => do
      let .valueArray values ← sptLookup ptr s.refs | none
      if index < 0 ∨ index.toNat ≥ values.length then none
      else write ptr (.valueArray (values.set index.toNat value))
  | .memOp (.mutCons tag index), values => do
      let child ← values[index]?
      allocate false (.mutBlock tag false (values.take index) child (values.drop (index + 1)))
  | .memOp .updateCons, [.refPtr _ ptr, .number index, value] => do
      let .mutBlock tag finalised left _ right ← sptLookup ptr s.refs | none
      if index ≠ Int.ofNat left.length ∨ finalised then none else
        write ptr (.mutBlock tag false left value right)
  | .memOp .finaliseCons, [value] => do
      let (value, refs, stamps) ← finaliseCons value s.refs s.tstamps
      some (value, { s with refs := refs, tstamps := stamps })
  | .intOp intop, values => (doIntApp intop values).bind result
  | .wordOp wordop, values => (doWordApp wordop values).bind result
  | .blockOp .boundsCheckBlock, [.block _ _ values, .number index] =>
      result (boolValue (decide (0 ≤ index ∧ index < Int.ofNat values.length)))
  | .memOp (.boundsCheckByte loose), [.refPtr _ ptr, .number index] => do
      let .byteArray _ bytes ← sptLookup ptr s.refs | none
      result (boolValue (decide (0 ≤ index ∧ if loose then index ≤ Int.ofNat bytes.length else index < Int.ofNat bytes.length)))
  | .memOp .boundsCheckArray, [.refPtr _ ptr, .number index] => do
      let .valueArray values ← sptLookup ptr s.refs | none
      result (boolValue (decide (0 ≤ index ∧ index < Int.ofNat values.length)))
  | .memOp .configGC, [.number _, .number _] => result unitValue
  | .thunkOp (.allocThunk mode), [value] =>
      if badThunkUpdate mode value s.refs then none else allocate false (.thunk mode value)
  | .thunkOp (.updateThunk mode), [.refPtr false ptr, value] =>
      if badThunkUpdate mode value s.refs then none else
        match sptLookup ptr s.refs with
        | some (.thunk .notEvaluated _) => write ptr (.thunk mode value)
        | _ => none
  | _, _ => none

/-- Primitive dispatcher including FFI final outcomes. -/
@[hol "cakeml/compiler/backend/semantics/dataSemScript.sml" "do_app_aux_def"]
noncomputable def doAppAux {C F : Type} (op : ClosLang.Op) (args : List Value)
    (s : State C F) : Result (Value × State C F) Value :=
  let fail : Result (Value × State C F) Value := .err (.abort .typeError)
  match op, args with
  | .ffi name, [.refPtr _ configPtr, .refPtr _ ptr] =>
      match sptLookup configPtr s.refs, sptLookup ptr s.refs with
      | some (.byteArray true config), some (.byteArray false bytes) =>
          match callFFIHOL s.ffi (.extCall name) config bytes with
          | .ret ffi updated => .val (unitValue, { s with refs := sptInsert ptr (.byteArray false updated) s.refs, ffi := ffi })
          | .final outcome => .err (.abort (.ffiError outcome))
      | _, _ => fail
  | .ffi _, _ => fail
  | _, _ => match applyNonFfi op args s with
      | some pair => .val pair
      | none => fail

end Flapjack.Compiler.Backend.DataSem

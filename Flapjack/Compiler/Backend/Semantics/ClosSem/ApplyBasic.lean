import Flapjack.Compiler.Backend.Semantics.ClosSem.State
import Flapjack.Compiler.Backend.Semantics.ClosSem.Int
import Flapjack.Compiler.Backend.Semantics.ClosSem.Word

/-! Global, block and numeric cases of the closure primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.ClosSem
open Flapjack.Basis.Pure.MlString Flapjack.SemanticPrimitivesHOL

/-- Decode the only two closure Boolean values. -/
def asBool : Value → Option Bool
  | .block 0 [] => some false
  | .block 1 [] => some true
  | _ => none

/-- Translate a closure constant to its runtime value. -/
def makeConst : ClosLang.Const → Value
  | .constInt value => .number value
  | .constWord64 value => .word64 value
  | .constStr value => .byteVector value.explode
  | .constCons tag values => .block tag (values.map makeConst)
termination_by c => sizeOf c

/-- Closure global operations; `none` denotes the original type error.
This is a proof-side dispatcher, pending finite-map and source review. -/
def applyGlobal {C F : Type} (op : ClosLang.GlobOp) (args : List Value) (state : State C F) :
    Option (Value × State C F) :=
  match op, args with
  | .global index, [] => (getGlobal index state.globals).join.map (fun value => (value, state))
  | .global _, [.number index] =>
    if index < 0 then none else (getGlobal index.toNat state.globals).join.map (fun value => (value, state))
  | .setGlobal index, [value] =>
    match getGlobal index state.globals with
    | some none => some (unitValue, { state with globals := state.globals.set index (some value) })
    | _ => none
  | .allocGlobal, [.number count] =>
    if count < 0 then none else some (unitValue, { state with globals := state.globals ++ List.replicate count.toNat none })
  | _, _ => none

/-- Closure block operations; `none` denotes the original type error. -/
def applyBlock {C F : Type} (op : ClosLang.BlockOp) (args : List Value) (state : State C F) :
    Option (Value × State C F) :=
  let result (value : Value) := some (value, state)
  match op, args with
  | .constant constant, [] => result (makeConst constant)
  | .cons tag, fields => result (.block tag fields)
  | .consExtend tag, .block _ fields :: .number lower :: .number len :: .number total :: initial =>
    if lower < 0 ∨ len < 0 ∨ Int.ofNat fields.length < lower + len ∨
        total = 0 ∨ total ≠ Int.ofNat initial.length + len then none
    else result (.block tag (initial ++ (fields.drop lower.toNat).take len.toNat))
  | .boolTest _, [a, b] => do
    let x ← asBool a
    let y ← asBool b
    result (boolValue (x == y))
  | .boolNot, [value] => (asBool value).bind (fun b => result (boolValue (!b)))
  | .elemAt index, [.block _ fields] => (fields[index]?).bind result
  | .listAppend, [a, b] => do
    let xs ← valueToList a
    let ys ← valueToList b
    result (listToValue (xs ++ ys))
  | .lengthBlock, [.block _ fields] => result (.number fields.length)
  | .fromList tag, [value] => (valueToList value).bind (fun xs => result (.block tag xs))
  | .tagEq tag, [.block actual _] => result (boolValue (actual == tag))
  | .lenEq length, [.block _ fields] => result (boolValue (fields.length == length))
  | .tagLenEq tag length, [.block actual fields] => result (boolValue (actual == tag && fields.length == length))
  | .equalConst (.int i), [.number j] => result (boolValue (decide (i = j)))
  | .equalConst (.w64 i), [.word64 j] => result (boolValue (decide (i = j)))
  | .equalConst (.str i), [.byteVector j] => result (boolValue (decide (j = i.explode)))
  | .equal, [a, b] => match doEq a b with
    | .val value => result (boolValue value)
    | .typeError => none
  | .boundsCheckBlock, [.block _ fields, .number i] =>
    result (boolValue (decide (0 ≤ i ∧ i < Int.ofNat fields.length)))
  | _, _ => none

/-- Integer and word operation cases, with the original floating-point model
assumptions. This partial dispatcher does not cover memory, FFI or thunks. -/
noncomputable def applyNumeric {C F : Type} (op : ClosLang.Op) (args : List Value) (state : State C F) :
    Option (Value × State C F) :=
  match op with
  | .intOp operation => (doIntApp operation args).map (fun value => (value, state))
  | .wordOp operation => (doWordApp operation args).map (fun value => (value, state))
  | _ => none

end Flapjack.Compiler.Backend.ClosSem

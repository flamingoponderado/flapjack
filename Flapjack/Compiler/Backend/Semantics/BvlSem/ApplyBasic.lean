import Flapjack.Compiler.Backend.Semantics.BvlSem.Build
import Flapjack.Compiler.Backend.Semantics.BvlSem.Equality
import Flapjack.Compiler.Backend.Semantics.BvlSem.Int
import Flapjack.Compiler.Backend.Semantics.BvlSem.Word
import Flapjack.Compiler.Backend.ClosToBvl.Constants

/-! Global, block, integer, and word branches of the BVL primitive dispatcher. -/
namespace Flapjack.Compiler.Backend.BvlSem
open Flapjack.Basis.Pure.MlString Flapjack.SemanticPrimitivesHOL

/-- Flapjack helper: decode precisely the two BVL Boolean values. -/
def asBool : Value → Option Bool
  | .block 0 [] => some false
  | .block 1 [] => some true
  | _ => none

/-- Source-shaped global branches of BVL `do_app`. `none` denotes the source
type error; full dispatcher correspondence awaits the remaining branches. -/
def applyGlobal {C F : Type} (op : ClosLang.GlobOp) (args : List Value) (s : State C F) :
    Option (Value × State C F) :=
  match op, args with
  | .global index, [] => (s.globals[index]?).join.map (fun value => (value, s))
  | .global _, [.number index] =>
    if index < 0 then none else
      (s.globals[index.toNat + ClosToBvl.numAddedGlobals]?).join.map (fun value => (value, s))
  | .setGlobal index, [value] =>
    match s.globals[index]? with
    | none => none
    | some _ => some (unitValue, { s with globals := s.globals.set index (some value) })
  | .allocGlobal, [.number count] =>
    if count < 0 then none else
      some (unitValue, { s with globals := s.globals ++ List.replicate count.toNat none })
  | _, _ => none

/-- Source-shaped block branches of BVL `do_app`. `none` denotes the source
type error; full dispatcher correspondence awaits the remaining branches. -/
noncomputable def applyBlock {C F : Type} (op : ClosLang.BlockOp) (args : List Value) (s : State C F) :
    Option (Value × State C F) :=
  let result (value : Value) := some (value, s)
  match op, args with
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
  | .build parts, [] =>
    let (value, refs) := doBuildConst parts s.refs
    some (value, { s with refs := refs })
  | .elemAt index, [.block _ fields] => fields[index]?.bind result
  | .elemAt index, [.refPtr _ ptr] =>
    match s.refs.lookup ptr with
    | some (.valueArray fields) => fields[index]?.bind result
    | _ => none
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
  | .equalConst (.str text), [.refPtr _ ptr] =>
    match s.refs.lookup ptr with
    | some (.byteArray true bytes) => result (boolValue (decide (bytes = text.explode)))
    | _ => none
  | .equal, [a, b] => match doEq s.refs a b with
    | .val value => result (boolValue value)
    | .typeError => none
  | .boundsCheckBlock, [.block _ fields, .number i] =>
    result (boolValue (decide (0 ≤ i ∧ i < Int.ofNat fields.length)))
  | _, _ => none

/-- Source-shaped integer and word branches of BVL `do_app`. -/
noncomputable def applyNumeric {C F : Type} (op : ClosLang.Op) (args : List Value) (s : State C F) :
    Option (Value × State C F) :=
  match op with
  | .intOp operation => (doIntApp operation args).map (fun value => (value, s))
  | .wordOp operation => (doWordApp operation args).map (fun value => (value, s))
  | _ => none

end Flapjack.Compiler.Backend.BvlSem

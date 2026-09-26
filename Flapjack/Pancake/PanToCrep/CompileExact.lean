import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.PanCommon

/-!
Exact-carrier expression lowering from HOL `PanLang.ExpHOL` to `CrepExpHOL`.

This belongs beside the production compiler as an exact source-semantics
counterpart. The production compiler remains separate until a kernel-checked
bridge and the full exact `compile_def` slice route are completed.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

/-! This module owns the exact-context carrier used by its tagged compiler so
    the finite-support qualifier is local to the declaration's module. Its
    fields and word/name carriers are the same ones as
    `PanToCrepContextExact`; the broad form below exists only for the required
    canonical finite-support roundtrip witness. -/

structure CompileExpContextBroad (width : Nat) where
  varsLookup : MlS → Option (ShapeHOL × List Nat)
  varsFiniteSupport : ∃ keys : List MlS, ∀ key, varsLookup key ≠ none → key ∈ keys
  funcsLookup : MlS → Option (List (MlS × ShapeHOL) × ShapeHOL)
  funcsFiniteSupport : ∃ keys : List MlS, ∀ key, funcsLookup key ≠ none → key ∈ keys
  eidsLookup : MlS → Option (BitVec width)
  eidsFiniteSupport : ∃ keys : List MlS, ∀ key, eidsLookup key ≠ none → key ∈ keys
  vmax : Nat

/-- Flapjack-specific carrier mirror of the tagged `PanToCrepContextExact`.
    It owns the finite-map fields in this module so the compiler's finite-map
    qualifier can be validated alongside its canonical witness. -/
structure CompileExpContextExact (width : Nat) [NeZero width] where
  vars : HolFiniteMapExact MlS (ShapeHOL × List Nat)
  funcs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL)
  eids : HolFiniteMapExact MlS (BitVec width)
  vmax : Nat

namespace CompileExpContextExact

def toBroad {width : Nat} [NeZero width] (context : CompileExpContextExact width) :
    CompileExpContextBroad width where
  varsLookup := context.vars.lookup
  varsFiniteSupport := context.vars.finiteSupport
  funcsLookup := context.funcs.lookup
  funcsFiniteSupport := context.funcs.finiteSupport
  eidsLookup := context.eids.lookup
  eidsFiniteSupport := context.eids.finiteSupport
  vmax := context.vmax

def ofBroad {width : Nat} [NeZero width] (context : CompileExpContextBroad width) :
    CompileExpContextExact width where
  vars := ⟨context.varsLookup, context.varsFiniteSupport⟩
  funcs := ⟨context.funcsLookup, context.funcsFiniteSupport⟩
  eids := ⟨context.eidsLookup, context.eidsFiniteSupport⟩
  vmax := context.vmax

/-- Canonical `HolFiniteMapExact` roundtrip required by the context qualifier. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) : ofBroad (toBroad context) = context := by
  cases context
  rfl

end CompileExpContextExact

/-! ### Exact-carrier `compile_exp_def`

The function below uses the HOL `ExpHOL`/`ShapeHOL` syntax, the finite-support
`PanToCrepContextExact`, and `CrepExpHOL` at the same positive word width. Its
equations follow `pan_to_crepScript.sml:39-101`: local lookup reads the exact
finite map; `compFieldHOL` and `loadShapeBytesHOLW` implement the cited HOL
helpers; and the bytes-in-word constant is `n2w (width DIV 8)`. This exact
definition does not by itself route the production compiler through the exact
carriers; that bridge remains tracked under the parent compile_def bead. -/

mutual
  /-- Exact width-indexed port of HOL `pan_to_crep$compile_exp_def`.
      `ShapeHOL`, `MlS`, and `CrepExpHOL width` preserve HOL's carriers and
      every fallback equation. -/
  @[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def"
    (fmap_as_finite_support := [vars, funcs, eids])]
  def compileExpExactHOLW {width : Nat} [NeZero width]
      (context : CompileExpContextExact width) :
      Flapjack.Pancake.PanLang.ExpHOL width →
        List (CrepExpHOL width) × Flapjack.Pancake.PanLang.ShapeHOL
    | .const value => ([.const value], .one)
    | .var .local name =>
        match context.vars.lookup name with
        | some (shape, names) => (names.map .var, shape)
        | none => ([.const (0 : BitVec width)], .one)
    | .var .global _ => ([.const (0 : BitVec width)], .one)
    | .rstruct expressions =>
        let compiled := compileExpExactHOLWList context expressions
        (compiled.flatMap Prod.fst, .comb (compiled.map Prod.snd))
    | .rfield index expression =>
        let compiled := compileExpExactHOLW context expression
        match compiled.2 with
        | .comb shapes => compFieldHOL index shapes compiled.1
        | _ => ([.const (0 : BitVec width)], .one)
    | .nstruct _ _ => ([.const (0 : BitVec width)], .one)
    | .nfield _ _ => ([.const (0 : BitVec width)], .one)
    | .load shape expression =>
        match compileExpExactHOLW context expression with
        | (address :: _, _) =>
            (loadShapeBytesHOLW (0 : BitVec width)
              (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape) address, shape)
        | ([], _) => ([.const (0 : BitVec width)], .one)
    | .load32 expression =>
        match compileExpExactHOLW context expression with
        | (address :: _, .one) => ([.load32 address], .one)
        | _ => ([.const (0 : BitVec width)], .one)
    | .loadByte expression =>
        match compileExpExactHOLW context expression with
        | (address :: _, .one) => ([.loadByte address], .one)
        | _ => ([.const (0 : BitVec width)], .one)
    | .op operator expressions =>
        match cexpHeads (compileExpExactHOLWList context expressions |>.map Prod.fst) with
        | some expressions => ([.op operator expressions], .one)
        | none => ([.const (0 : BitVec width)], .one)
    | .panop operator expressions =>
        match cexpHeads (compileExpExactHOLWList context expressions |>.map Prod.fst) with
        | some expressions => ([.crepOp (compilePanOp operator) expressions], .one)
        | none => ([.const (0 : BitVec width)], .one)
    | .cmp operator left right =>
        match compileExpExactHOLW context left, compileExpExactHOLW context right with
        | (left :: _, _), (right :: _, _) => ([.cmp operator left right], .one)
        | _, _ => ([.const (0 : BitVec width)], .one)
    | .shift operator left right =>
        match compileExpExactHOLW context left, compileExpExactHOLW context right with
        | (left :: _, _), (right :: _, _) => ([.shift operator left right], .one)
        | _, _ => ([.const (0 : BitVec width)], .one)
    | .baseAddr => ([.baseAddr], .one)
    | .topAddr => ([.topAddr], .one)
    | .bytesInWord => ([.const (BitVec.ofNat width (width / 8))], .one)
  termination_by expression => sizeOf expression
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial

  /-- `MAP (compile_exp ctxt)` in HOL's RStruct/Op/Panop equations. -/
  def compileExpExactHOLWList {width : Nat} [NeZero width]
      (context : CompileExpContextExact width) :
      List (Flapjack.Pancake.PanLang.ExpHOL width) →
        List (List (CrepExpHOL width) × Flapjack.Pancake.PanLang.ShapeHOL)
    | [] => []
    | expression :: expressions =>
        compileExpExactHOLW context expression ::
          compileExpExactHOLWList context expressions
  termination_by expressions => sizeOf expressions
  decreasing_by
    all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-! The direct `Return` case of `compile_def` (`pan_to_crepScript.sml:193-196`).
    This helper is untagged because it exposes one exact equation slice rather
    than HOL's complete recursive `compile` definition. -/

def compileReturnExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (expression : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  let (expressions, shape) := compileExpExactHOLW context expression
  if Flapjack.Pancake.PanLang.sizeOfShapeHOL shape = 0 then .return []
  else .return expressions

/-! These helpers expose the paired `Store32`/`StoreByte` equations from
    `compile_def` (`pan_to_crepScript.sml:185-192`). Each emits its target
    instruction only when both recursively compiled expression lists have a
    head, otherwise returning `Skip` as HOL does. They remain untagged slices. -/

def compileStore32ExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (destination source : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  match compileExpExactHOLW context destination, compileExpExactHOLW context source with
  | (address :: _, _), (value :: _, _) => .store32 address value
  | _, _ => .skip

def compileStoreByteExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (destination source : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  match compileExpExactHOLW context destination, compileExpExactHOLW context source with
  | (address :: _, _), (value :: _, _) => .storeByte address value
  | _, _ => .skip

/-! The `If` and `While` equations from `compile_def`
    (`pan_to_crepScript.sml:209-218`). The target branches/body are explicit
    recursive results; each helper keeps only the head of the exact compiled
    condition and returns `Skip` when no condition head exists. These are
    equation slices, not the assembled recursive compiler. -/

def compileIfExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (condition : Flapjack.Pancake.PanLang.ExpHOL width)
    (thenBranch elseBranch : CrepProgHOL width) : CrepProgHOL width :=
  match compileExpExactHOLW context condition with
  | (condition :: _, _) => .ite condition thenBranch elseBranch
  | ([], _) => .skip

def compileWhileExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (condition : Flapjack.Pancake.PanLang.ExpHOL width)
    (body : CrepProgHOL width) : CrepProgHOL width :=
  match compileExpExactHOLW context condition with
  | (condition :: _, _) => .while condition body
  | ([], _) => .skip

/-! Two constant `Skip` equations from `compile_def`: Global Assign
    (`pan_to_crepScript.sml:163`) and Global ShMemLoad (line 305). They are
    explicit untagged slices; their source/context inputs are retained while
    the compiled result is independent of them, exactly as in HOL. -/

def compileGlobalAssignExactHOLW {width : Nat} [NeZero width]
    (_context : CompileExpContextExact width) (_name : MlS)
    (_expression : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width := .skip

def compileGlobalShMemLoadExactHOLW {width : Nat} [NeZero width]
    (_context : CompileExpContextExact width) (_operator : OpSize) (_name : MlS)
    (_address : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width := .skip

/-! The `Assign Local` clause from `compile_def`
    (`pan_to_crepScript.sml:153-162`). It preserves the destination-name
    lookup and compiled-list length checks. When destination variables do not
    occur in the right-hand expressions, assignments are emitted directly;
    otherwise HOL first copies through fresh `vmax + SUC i` temporaries. -/

def compileLocalAssignExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (name : MlS)
    (expression : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  let (expressions, _shape) := compileExpExactHOLW context expression
  match context.vars.lookup name with
  | none => .skip
  | some (_shape, names) =>
      if names.length != expressions.length then .skip
      else
        let expressionVars := expressions.flatMap fun compiled =>
          crepExpVarsW (crepExpOfHOL compiled)
        if distinctListsHol names expressionVars then
          crepNestedSeqHOL (List.zipWith CrepProgHOL.assign names expressions)
        else
          let temporaries := (List.range names.length).map
            (fun index => context.vmax + index + 1)
          let assignments := List.zipWith CrepProgHOL.assign names
            (temporaries.map CrepExpHOL.var)
          nestedDecsHOL temporaries expressions (crepNestedSeqHOL assignments)

/-! The local `Primitive` destination equation from `compile_def`
    (`pan_to_crepScript.sml:165-175`). HOL flattens every argument's compiled
    expression list, allocates one fresh temporary per flattened value, then
    wraps the target primitive in `nested_decs`. -/

def compilePrimitiveExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (name : MlS) (operator : PrimOp)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width)) : CrepProgHOL width :=
  let values := (compileExpExactHOLWList context arguments).flatMap Prod.fst
  match context.vars.lookup name with
  | none => .skip
  | some (_shape, names) =>
      let temporaries := (List.range values.length).map
        (fun index => context.vmax + index + 1)
      nestedDecsHOL temporaries values (.primitive names operator temporaries)

/-! The recursive `Store` clause from `compile_def`
    (`pan_to_crepScript.sml:177-185`). The address must compile to a head;
    the value list must have exactly its shape size. HOL reserves `vmax+1`
    for the address and generates the remaining temporaries from that base. -/

def compileStoreExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width)
    (address value : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  match compileExpExactHOLW context address with
  | (compiledAddress :: _, _) =>
      let (values, shape) := compileExpExactHOLW context value
      let valueCount := Flapjack.Pancake.PanLang.sizeOfShapeHOL shape
      let addressName := context.vmax + 1
      let valueNames := (List.range valueCount).map
        (fun index => addressName + index + 1)
      if valueCount != values.length then .skip
      else
        let storeSequence := crepNestedSeqHOL
          (storesHOL (.var addressName) (valueNames.map CrepExpHOL.var) (0 : BitVec width))
        nestedDecsHOL (addressName :: valueNames) (compiledAddress :: values) storeSequence
  | ([], _) => .skip

end Flapjack

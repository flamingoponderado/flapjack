import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.PanToCrep.ExpHdlExact
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

/-- Convert the compiler-local qualifier carrier to the tagged HOL `context`.
    This is a field-preserving conversion, not a production String codec. -/
def toPanToCrep {width : Nat} [NeZero width] (context : CompileExpContextExact width) :
    PanToCrepContextExact width where
  vars := context.vars
  funcs := context.funcs
  eids := context.eids
  vmax := context.vmax

/-- Convert the tagged HOL `context` to the local carrier required by the
    current same-module finite-support witness checker. -/
def ofPanToCrep {width : Nat} [NeZero width] (context : PanToCrepContextExact width) :
    CompileExpContextExact width where
  vars := context.vars
  funcs := context.funcs
  eids := context.eids
  vmax := context.vmax

theorem ofPanToCrep_toPanToCrep {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) :
    ofPanToCrep (toPanToCrep context) = context := by
  cases context
  rfl

theorem toPanToCrep_ofPanToCrep {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    toPanToCrep (ofPanToCrep context) = context := by
  cases context
  rfl

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

/-! The `Raise` clause from `compile_def`
    (`pan_to_crepScript.sml:197-207`). It requires an exception-id lookup and
    a shape size matching the compiled value list, then saves each component
    into consecutive globals before raising the looked-up word code. -/

def compileRaiseExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (exceptionName : MlS)
    (expression : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  match context.eids.lookup exceptionName with
  | none => .skip
  | some exceptionCode =>
      let (values, shape) := compileExpExactHOLW context expression
      let valueCount := Flapjack.Pancake.PanLang.sizeOfShapeHOL shape
      let temporaries := (List.range valueCount).map
        (fun index => context.vmax + index + 1)
      if valueCount != values.length then .skip
      else
        let saveValues := crepNestedSeqHOL
          (storeGlobalsHOL (0 : BitVec 5) (temporaries.map CrepExpHOL.var))
        .seq (nestedDecsHOL temporaries values saveValues) (.raise exceptionCode)

/-! The `ShMemStore` clause from `compile_def`
    (`pan_to_crepScript.sml:285-293`). Both operands must compile to heads.
    HOL picks the first compiled value and address, then places the store at
    one greater than the largest variable used by the value expression. -/

def compileShMemStoreExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (operator : OpSize)
    (value address : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  match compileExpExactHOLW context value, compileExpExactHOLW context address with
  | (compiledValue :: _, _), (compiledAddress :: _, _) =>
      let index := (crepExpVarsW (crepExpOfHOL compiledValue)).foldr max 0
      .dec (index + 1) compiledAddress
        (.shMem (storeMemOpHOL operator) (index + 1) compiledValue)
  | _, _ => .skip

/-! The local `ShMemLoad` clause from `compile_def`
    (`pan_to_crepScript.sml:296-304`). It takes the first compiled address and
    first destination variable, preserving both lookup/head fallbacks. -/

def compileShMemLoadExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (operator : OpSize) (name : MlS)
    (address : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  match compileExpExactHOLW context address with
  | (compiledAddress :: _, _) =>
      match context.vars.lookup name with
      | some (_, destination :: _) =>
          .shMem (loadMemOpHOL operator) destination compiledAddress
      | _ => .skip
  | ([], _) => .skip

/-! The recursive `Dec` clause from `compile_def`
    (`pan_to_crepScript.sml:145-152`). It allocates names from the old `vmax`,
    extends the variable map and `vmax` for the recursive body, and emits the
    declaration only when the compiled expression count matches the shape. -/

def compileDecExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (name : MlS)
    (shape : Flapjack.Pancake.PanLang.ShapeHOL)
    (expression : Flapjack.Pancake.PanLang.ExpHOL width)
    (compileBody : CompileExpContextExact width → CrepProgHOL width) : CrepProgHOL width :=
  let (values, compiledShape) := compileExpExactHOLW context expression
  let valueCount := Flapjack.Pancake.PanLang.sizeOfShapeHOL compiledShape
  let names := (List.range valueCount).map (fun index => context.vmax + index + 1)
  let bodyContext : CompileExpContextExact width :=
    { context with
      vars := context.vars.update (name, (shape, names))
      vmax := context.vmax + valueCount }
  if valueCount != values.length then .skip
  else nestedDecsHOL names values (compileBody bodyContext)

/-! The `DecCall` clause from HOL `compile_def`
    (`pan_to_crepScript.sml:262-272`). It allocates return names from the old
    `vmax`, compiles the body under the extended variable map and `vmax`,
    initializes every return slot to zero, then emits the target Call followed
    by the compiled body. -/

def compileDecCallExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (name : MlS)
    (shape : Flapjack.Pancake.PanLang.ShapeHOL) (function : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (compileBody : CompileExpContextExact width → CrepProgHOL width) :
    CrepProgHOL width :=
  let compiledArguments := compileExpExactHOLWList context arguments
  let arguments := compiledArguments.flatMap Prod.fst
  let returnCount := Flapjack.Pancake.PanLang.sizeOfShapeHOL shape
  let names := (List.range returnCount).map
    (fun index => context.vmax + index + 1)
  let bodyContext : CompileExpContextExact width :=
    { context with
      vars := context.vars.update (name, (shape, names))
      vmax := context.vmax + returnCount }
  let returnDeclarations := nestedDecsHOL names
    (List.replicate names.length (.const (0 : BitVec width)))
  let call := CrepProgHOL.call (some (names, none)) function arguments
  returnDeclarations (.seq call (compileBody bodyContext))

/-! The `rtyp = NONE` arm of the HOL `Call` clause
    (`pan_to_crepScript.sml:221-225`) compiles each argument, flattens its
    expression list, and emits a tail call with no return metadata. -/

def compileCallNoReturnExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width)) :
    CrepProgHOL width :=
  let compiledArguments := compileExpExactHOLWList context arguments
  let flattenedArguments := compiledArguments.flatMap Prod.fst
  .call none function flattenedArguments

/-! Exact source-level form of HOL `wrap_rt_def` (`pan_to_crepScript.sml:131-136`).
    It removes only a missing lookup and the special `(One, [])` result. -/

def wrapRtExactHOL (result : Option (Flapjack.Pancake.PanLang.ShapeHOL × List Nat)) :=
  match result with
  | none => none
  | some (.one, []) => none
  | other => other

/-! The successful `wrap_rt (FLOOKUP ctxt.vars rt)` arm with no handler in HOL
    `compile_def` (`pan_to_crepScript.sml:252-261`). It reuses the destination
    names directly in Call metadata and does not allocate or initialize return
    slots. The premise captures precisely the successful wrapped lookup. -/

def compileCallWrappedResultNoHandlerExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function resultName : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (resultShape : Flapjack.Pancake.PanLang.ShapeHOL) (resultNames : List Nat)
    (_wrappedResult : wrapRtExactHOL (context.vars.lookup resultName) =
      some (resultShape, resultNames)) : CrepProgHOL width :=
  let compiledArguments := compileExpExactHOLWList context arguments
  let flattenedArguments := compiledArguments.flatMap Prod.fst
  .call (some (resultNames, none)) function flattenedArguments

/-! The `rtyp = SOME (NONE, NONE)` arm of the HOL `Call` clause
    (`pan_to_crepScript.sml:226-232`) looks up the callee's return shape,
    allocates result names above `vmax`, initializes those names to zero, and
    emits a call with result metadata. -/

def compileCallResultNoHandlerExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width)) :
    CrepProgHOL width :=
  let compiledArguments := compileExpExactHOLWList context arguments
  let flattenedArguments := compiledArguments.flatMap Prod.fst
  let returnShape := (context.funcs.lookup function).map Prod.snd
  let returnNames := match returnShape with
    | none => []
    | some shape => (List.range (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape)).map
        (fun index => context.vmax + index + 1)
  let returnDeclarations := nestedDecsHOL returnNames
    (List.replicate returnNames.length (.const (0 : BitVec width)))
  returnDeclarations
    (.call (some (returnNames, none)) function flattenedArguments)

/-! The `hdl = SOME (eid, evar, p)` branch with no `eids` lookup result from
    HOL `compile_def` (`pan_to_crepScript.sml:233-235`) discards the handler and
    falls back to the same zero-initialized result call as the `hdl = NONE`
    case. The premise exposes exactly that HOL lookup side condition. -/

def compileCallHandlerMissingEidExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (_exceptionName _exceptionVariable : MlS)
    (_handlerBody : Flapjack.Pancake.PanLang.ProgHOL width)
    (_missingEid : context.eids.lookup _exceptionName = none) :
    CrepProgHOL width :=
  compileCallResultNoHandlerExactHOLW context function arguments

/-! The `hdl = SOME (eid, evar, p)` branch with a successful `eids` lookup in
    HOL `compile_def` (`pan_to_crepScript.sml:233-239`) keeps the exception
    handler. It wraps the recursively compiled body with exact `exp_hdl`, then
    zero-initializes the callee return names before emitting the handled call. -/

def compileCallHandlerPresentEidExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (exceptionName exceptionVariable : MlS) (exceptionCode : BitVec width)
    (_eidLookup : context.eids.lookup exceptionName = some exceptionCode)
    (compileHandlerBody : CompileExpContextExact width → CrepProgHOL width) :
    CrepProgHOL width :=
  let compiledArguments := compileExpExactHOLWList context arguments
  let flattenedArguments := compiledArguments.flatMap Prod.fst
  let returnShape := (context.funcs.lookup function).map Prod.snd
  let returnNames := match returnShape with
    | none => []
    | some shape => (List.range (Flapjack.Pancake.PanLang.sizeOfShapeHOL shape)).map
        (fun index => context.vmax + index + 1)
  let handler := CrepProgHOL.seq
    (expHdlExact ⟨context.vars⟩ exceptionVariable)
    (compileHandlerBody context)
  let call := CrepProgHOL.call
    (some (returnNames, some (exceptionCode, handler))) function flattenedArguments
  nestedDecsHOL returnNames
    (List.replicate returnNames.length (.const (0 : BitVec width))) call

/-! The `ExtCall` clause from HOL `compile_def`
    (`pan_to_crepScript.sml:274-290`). The freshness bound is the maximum over
    every variable in all four compiled operand lists, even though the output
    uses only each list's head. All four source shapes must be `One` and all
    four compiled lists must be nonempty; otherwise HOL returns `Skip`. -/

def compileExtCallExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function : MlS)
    (configuration configurationLength array arrayLength :
      Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  let (configurationValues, configurationShape) :=
    compileExpExactHOLW context configuration
  let (configurationLengthValues, configurationLengthShape) :=
    compileExpExactHOLW context configurationLength
  let (arrayValues, arrayShape) := compileExpExactHOLW context array
  let (arrayLengthValues, arrayLengthShape) :=
    compileExpExactHOLW context arrayLength
  let allValues := configurationValues ++ configurationLengthValues ++
    arrayValues ++ arrayLengthValues
  let allVariables := allValues.flatMap fun value =>
    crepExpVarsW (crepExpOfHOL value)
  let maximumVariable := allVariables.foldl (fun maximum variableIndex =>
    Nat.max maximum variableIndex) 0
  match configurationShape, configurationValues,
      configurationLengthShape, configurationLengthValues,
      arrayShape, arrayValues, arrayLengthShape, arrayLengthValues with
  | .one, configurationValue :: _, .one, configurationLengthValue :: _,
      .one, arrayValue :: _, .one, arrayLengthValue :: _ =>
        .dec (maximumVariable + 1) configurationValue
          (.dec (maximumVariable + 2) configurationLengthValue
            (.dec (maximumVariable + 3) arrayValue
              (.dec (maximumVariable + 4) arrayLengthValue
                (.extCall function (maximumVariable + 1) (maximumVariable + 2)
                  (maximumVariable + 3) (maximumVariable + 4)))))
  | _, _, _, _, _, _, _, _ => .skip

end Flapjack

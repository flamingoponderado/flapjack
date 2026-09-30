import Flapjack.Pancake.CrepInline.Canonical
import Flapjack.Pancake.PanToCrep.Compile
import Flapjack.Pancake.PanToCrep.ContextExact
import Flapjack.Pancake.PanToCrep.MakeVmapHOL
import Flapjack.Pancake.PanToCrep.ExpHdlExact
import Flapjack.Pancake.Semantics.CrepSem.HOLState
import Flapjack.Pancake.PanCommon

/-!
Exact-carrier expression lowering from HOL `PanLang.ExpHOL` to `CrepExpHOL`.

The parser-proved compiler entry executes this lowering transitively through
`compileProgExactHOLW` before decoding its result to production Crep. The
per-function and top-level output-preservation bridges live in `CompileProg`.
Direct callers without byte-range evidence retain the untagged String-backed
compatibility route; the broader `compile_prog` carrier gap is tracked
separately for exact `compile_inl_top`.
-/

namespace Flapjack

open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang

/-! The exact compiler reuses the canonical tagged HOL context carrier from
    `ContextExact.lean`; it no longer defines a duplicate structure solely to
    host a local finite-support witness. Keep this source-level alias for test
    fixtures that used the earlier descriptive name. -/

abbrev CompileExpContextExact (width : Nat) [NeZero width] :=
  PanToCrepContextExact width

/-- Same-module witness for the imported canonical carrier. This delegates to
    the checked `PanToCrepContextExact` roundtrip and lets the qualifier checker
    validate the actual imported owner and fields at each tagged declaration. -/
theorem holFmapAsFiniteSupportWitness {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    PanToCrepContextExact.ofBroad (PanToCrepContextExact.toBroad context) = context :=
  PanToCrepContextExact.holFmapAsFiniteSupportWitness context

/-! ### Exact-carrier `compile_exp_def`

The function below uses the HOL `ExpHOL`/`ShapeHOL` syntax, the finite-support
`PanToCrepContextExact`, and `CrepExpHOL` at the same positive word width. Its
equations follow `pan_to_crepScript.sml:39-101`: local lookup reads the exact
finite map; `compFieldHOL` and `loadShapeBytesHOLW` implement the cited HOL
helpers; and the bytes-in-word constant is `n2w (width DIV 8)`. The parser-proved
production body route calls this definition through `compileProgExactHOLW`; the
output-preservation bridge is recorded in `CompileProg.lean`. -/

mutual
  /-- Exact width-indexed port of HOL `pan_to_crep$compile_exp_def`.
      `ShapeHOL`, `MlS`, and `CrepExpHOL width` preserve HOL's carriers and
      every fallback equation. -/
  @[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_exp_def"
    (fmap_as_finite_support := [vars, funcs, eids])
    (words_as_type_indexed_bitvec)]
  def compileExpExactHOLW {width : Nat} [NeZero width]
      (context : PanToCrepContextExact width) :
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
      (context : PanToCrepContextExact width) :
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
    (context : PanToCrepContextExact width)
    (expression : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  let (expressions, shape) := compileExpExactHOLW context expression
  if Flapjack.Pancake.PanLang.sizeOfShapeHOL shape = 0 then .return []
  else .return expressions

/-! These helpers expose the paired `Store32`/`StoreByte` equations from
    `compile_def` (`pan_to_crepScript.sml:185-192`). Each emits its target
    instruction only when both recursively compiled expression lists have a
    head, otherwise returning `Skip` as HOL does. They remain untagged slices. -/

def compileStore32ExactHOLW {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
    (destination source : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width :=
  match compileExpExactHOLW context destination, compileExpExactHOLW context source with
  | (address :: _, _), (value :: _, _) => .store32 address value
  | _, _ => .skip

def compileStoreByteExactHOLW {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
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
    (context : PanToCrepContextExact width)
    (condition : Flapjack.Pancake.PanLang.ExpHOL width)
    (thenBranch elseBranch : CrepProgHOL width) : CrepProgHOL width :=
  match compileExpExactHOLW context condition with
  | (condition :: _, _) => .ite condition thenBranch elseBranch
  | ([], _) => .skip

def compileWhileExactHOLW {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width)
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
    (_context : PanToCrepContextExact width) (_name : MlS)
    (_expression : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width := .skip

def compileGlobalShMemLoadExactHOLW {width : Nat} [NeZero width]
    (_context : PanToCrepContextExact width) (_operator : OpSize) (_name : MlS)
    (_address : Flapjack.Pancake.PanLang.ExpHOL width) : CrepProgHOL width := .skip

/-! The `Assign Local` clause from `compile_def`
    (`pan_to_crepScript.sml:153-162`). It preserves the destination-name
    lookup and compiled-list length checks. When destination variables do not
    occur in the right-hand expressions, assignments are emitted directly;
    otherwise HOL first copies through fresh `vmax + SUC i` temporaries. -/

def compileLocalAssignExactHOLW {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : MlS)
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
    (context : PanToCrepContextExact width) (name : MlS) (operator : PrimOp)
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
    (context : PanToCrepContextExact width)
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
    (context : PanToCrepContextExact width) (exceptionName : MlS)
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
    (context : PanToCrepContextExact width) (operator : OpSize)
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
    (context : PanToCrepContextExact width) (operator : OpSize) (name : MlS)
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
    declaration only when the compiled expression count matches the shape.

    HOL ignores the declared shape `s` of `Dec v s e p` and stores the shape
    `sh` produced by `compile_exp` in the extended variable map
    (`nctxt = ctxt with <|vars := ctxt.vars |+ (v, (sh, nvars)); ...|>`), and
    production `compileProgHOL` does the same with `compiled.2`. To stay exact,
    the `_shape` parameter is unused here and the compiled shape is stored. -/

def compileDecExactHOLW {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (name : MlS)
    (_shape : Flapjack.Pancake.PanLang.ShapeHOL)
    (expression : Flapjack.Pancake.PanLang.ExpHOL width)
    (compileBody : PanToCrepContextExact width → CrepProgHOL width) : CrepProgHOL width :=
  let (values, compiledShape) := compileExpExactHOLW context expression
  let valueCount := Flapjack.Pancake.PanLang.sizeOfShapeHOL compiledShape
  let names := (List.range valueCount).map (fun index => context.vmax + index + 1)
  let bodyContext : PanToCrepContextExact width :=
    { context with
      vars := context.vars.update (name, (compiledShape, names))
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

/-! The successful `wrap_rt (FLOOKUP ctxt.vars rt)` arm with no handler in HOL
    `compile_def` (`pan_to_crepScript.sml:252-261`). It reuses the destination
    names directly in Call metadata and does not allocate or initialize return
    slots. The premise uses the canonical tagged `wrapRtHOL` port. -/

def compileCallWrappedResultNoHandlerExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function resultName : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (resultShape : Flapjack.Pancake.PanLang.ShapeHOL) (resultNames : List Nat)
    (_wrappedResult : wrapRtHOL (context.vars.lookup resultName) =
      some (resultShape, resultNames)) : CrepProgHOL width :=
  let compiledArguments := compileExpExactHOLWList context arguments
  let flattenedArguments := compiledArguments.flatMap Prod.fst
  .call (some (resultNames, none)) function flattenedArguments

/-! The `NONE` arm of `wrap_rt (FLOOKUP ctxt.vars rt)` in HOL `compile_def`
    (`pan_to_crepScript.sml:252-261`). Missing names and `(One, [])` both emit a
    tail Call with flattened arguments and no return metadata, using the
    canonical tagged `wrapRtHOL` port for the side condition. -/

def compileCallWrappedResultFallbackNoHandlerExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function resultName : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (_wrappedResult : wrapRtHOL (context.vars.lookup resultName) = none) :
    CrepProgHOL width :=
  let compiledArguments := compileExpExactHOLWList context arguments
  let flattenedArguments := compiledArguments.flatMap Prod.fst
  .call none function flattenedArguments

/-! The handler-present Call arm with a successful wrapped result lookup but a
    missing exception-code lookup in HOL `compile_def` (`pan_to_crepScript.sml:252-261`).
    HOL discards the handler while retaining the destination names as result
    metadata. -/

def compileCallWrappedResultHandlerMissingEidExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function resultName : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (resultShape : Flapjack.Pancake.PanLang.ShapeHOL) (resultNames : List Nat)
    (exceptionName _exceptionVariable : MlS)
    (_handlerBody : Flapjack.Pancake.PanLang.ProgHOL width)
    (_wrappedResult : wrapRtHOL (context.vars.lookup resultName) =
      some (resultShape, resultNames))
    (_missingEid : context.eids.lookup exceptionName = none) : CrepProgHOL width :=
  compileCallWrappedResultNoHandlerExactHOLW context function resultName arguments
    resultShape resultNames _wrappedResult

/-! The handler-present Call arm with successful wrapped-result and exception
    code lookups in HOL `compile_def` (`pan_to_crepScript.sml:252-261`). It keeps
    the destination names directly and sequences exact `exp_hdl` with the
    recursively compiled handler body, without return-slot declarations. -/

def compileCallWrappedResultHandlerPresentEidExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function resultName : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (resultShape : Flapjack.Pancake.PanLang.ShapeHOL) (resultNames : List Nat)
    (exceptionName exceptionVariable : MlS) (exceptionCode : BitVec width)
    (_wrappedResult : wrapRtHOL (context.vars.lookup resultName) =
      some (resultShape, resultNames))
    (_eidLookup : context.eids.lookup exceptionName = some exceptionCode)
    (compileHandlerBody : CompileExpContextExact width → CrepProgHOL width) :
    CrepProgHOL width :=
  let compiledArguments := compileExpExactHOLWList context arguments
  let flattenedArguments := compiledArguments.flatMap Prod.fst
  let handler := CrepProgHOL.seq
    (expHdlExact context.vars exceptionVariable)
    (compileHandlerBody context)
  .call (some (resultNames, some (exceptionCode, handler))) function flattenedArguments

/-! The wrapped-result `NONE` arm with a found handler EID in HOL `compile_def`
    (`pan_to_crepScript.sml:252-261`). HOL keeps the handler but supplies an
    empty return-name list to Call metadata. -/

def compileCallWrappedResultFallbackHandlerPresentEidExactHOLW
    {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function resultName : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (exceptionName exceptionVariable : MlS) (exceptionCode : BitVec width)
    (_wrappedResult : wrapRtHOL (context.vars.lookup resultName) = none)
    (_eidLookup : context.eids.lookup exceptionName = some exceptionCode)
    (compileHandlerBody : CompileExpContextExact width → CrepProgHOL width) :
    CrepProgHOL width :=
  let compiledArguments := compileExpExactHOLWList context arguments
  let flattenedArguments := compiledArguments.flatMap Prod.fst
  let handler := CrepProgHOL.seq
    (expHdlExact context.vars exceptionVariable)
    (compileHandlerBody context)
  .call (some ([], some (exceptionCode, handler))) function flattenedArguments

/-! The wrapped-result `NONE` arm with a missing handler EID in HOL
    `compile_def` (`pan_to_crepScript.sml:252-261`). HOL drops both handler and
    return metadata and emits a flattened tail call. -/

def compileCallWrappedResultFallbackHandlerMissingEidExactHOLW
    {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function resultName : MlS)
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (exceptionName _exceptionVariable : MlS)
    (_handlerBody : Flapjack.Pancake.PanLang.ProgHOL width)
    (_wrappedResult : wrapRtHOL (context.vars.lookup resultName) = none)
    (_missingEid : context.eids.lookup exceptionName = none) : CrepProgHOL width :=
  compileCallWrappedResultFallbackNoHandlerExactHOLW context function resultName
    arguments _wrappedResult

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
    (expHdlExact context.vars exceptionVariable)
    (compileHandlerBody context)
  let call := CrepProgHOL.call
    (some (returnNames, some (exceptionCode, handler))) function flattenedArguments
  nestedDecsHOL returnNames
    (List.replicate returnNames.length (.const (0 : BitVec width))) call

/-! ### Assembled exact `Call` info equation

This dispatcher combines the source-reviewed `Call` arm slices above in the
same nesting as HOL `compile_def` (`pan_to_crepScript.sml:221-261`). In
particular, the assigned-result kind is ignored by `wrap_rt`; handler lookup
occurs only after the result-shape branch; and a handler body remains a
recursive compiler callback until the full `compile_def` assembly is ported.
This is an equation slice, not yet a recursive `compile` definition. -/

def compileCallInfoExactHOLW {width : Nat} [NeZero width]
    (context : CompileExpContextExact width) (function : MlS)
    (info : Option (Option (VarKind × MlS) ×
      Option (MlS × MlS × Flapjack.Pancake.PanLang.ProgHOL width)))
    (arguments : List (Flapjack.Pancake.PanLang.ExpHOL width))
    (compileBody : CompileExpContextExact width →
      Flapjack.Pancake.PanLang.ProgHOL width → CrepProgHOL width) :
    CrepProgHOL width :=
  match info with
  | none => compileCallNoReturnExactHOLW context function arguments
  | some (none, none) =>
      compileCallResultNoHandlerExactHOLW context function arguments
  | some (none, some (exceptionName, exceptionVariable, body)) =>
      match hEid : context.eids.lookup exceptionName with
      | none =>
          compileCallHandlerMissingEidExactHOLW context function arguments
            exceptionName exceptionVariable body
            hEid
      | some exceptionCode =>
          compileCallHandlerPresentEidExactHOLW context function arguments
            exceptionName exceptionVariable exceptionCode
            hEid
            (fun bodyContext => compileBody bodyContext body)
  | some (some (_resultKind, resultName), handler) =>
      match hWrap : wrapRtHOL (context.vars.lookup resultName) with
      | none =>
          match handler with
          | none =>
              compileCallWrappedResultFallbackNoHandlerExactHOLW context
                function resultName arguments hWrap
          | some (exceptionName, exceptionVariable, body) =>
              match hEid : context.eids.lookup exceptionName with
              | none =>
                  compileCallWrappedResultFallbackHandlerMissingEidExactHOLW
                    context function resultName arguments exceptionName
                    exceptionVariable body hWrap hEid
              | some exceptionCode =>
                  compileCallWrappedResultFallbackHandlerPresentEidExactHOLW
                    context function resultName arguments exceptionName
                    exceptionVariable exceptionCode hWrap hEid
                    (fun bodyContext => compileBody bodyContext body)
      | some (resultShape, resultNames) =>
          match handler with
          | none =>
              compileCallWrappedResultNoHandlerExactHOLW context function
                resultName arguments resultShape resultNames hWrap
          | some (exceptionName, exceptionVariable, body) =>
              match hEid : context.eids.lookup exceptionName with
              | none =>
                  compileCallWrappedResultHandlerMissingEidExactHOLW context
                    function resultName arguments resultShape resultNames
                    exceptionName exceptionVariable body hWrap hEid
              | some exceptionCode =>
                  compileCallWrappedResultHandlerPresentEidExactHOLW context
                    function resultName arguments resultShape resultNames
                    exceptionName exceptionVariable exceptionCode hWrap hEid
                    (fun bodyContext => compileBody bodyContext body)

/-! The `ExtCall` clause from HOL `compile_def`
    (`pan_to_crepScript.sml:274-290`). The freshness bound is the maximum over
    every variable in all four compiled operand lists, even though the output
    uses only each list's head. All four source shapes must be `One` and all
    four compiled lists must be nonempty; otherwise HOL returns `Skip`. -/

def compileExtCallExactHOLW {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) (function : MlS)
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

/-! ### Exact recursive `compile_def`

Every constructor equation below was source-reviewed against
`cakeml/pancake/pan_to_crepScript.sml:139-307` and its exact helper slice above.
The only representation qualifier is the exact finite-support carrier for
HOL's three finite maps; the syntax, positive word width, names, and output
carrier are otherwise constructor-for-constructor HOL translations. The
parser-backed `flapjack-compile` route executes this definition through
`compileProgTopHOLProductionExact` after the byte-range and output-codec
bridges; arbitrary String-backed callers retain the untagged compatibility
path. -/

@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_def"
  (fmap_as_finite_support := [vars, funcs, eids])
  (words_as_type_indexed_bitvec)]
def compileProgExactHOLW {width : Nat} [NeZero width]
    (context : PanToCrepContextExact width) :
    Flapjack.Pancake.PanLang.ProgHOL width → CrepProgHOL width
  | .skip => .skip
  | .dec name shape expression body =>
      compileDecExactHOLW context name shape expression
        (fun bodyContext => compileProgExactHOLW bodyContext body)
  | .assign .local name expression =>
      compileLocalAssignExactHOLW context name expression
  | .assign .global name expression =>
      compileGlobalAssignExactHOLW context name expression
  | .primitive name operator arguments =>
      compilePrimitiveExactHOLW context name operator arguments
  | .store address value => compileStoreExactHOLW context address value
  | .store32 address value => compileStore32ExactHOLW context address value
  | .storeByte address value => compileStoreByteExactHOLW context address value
  | .seq first second =>
      .seq (compileProgExactHOLW context first) (compileProgExactHOLW context second)
  | .ite condition thenBranch elseBranch =>
      compileIfExactHOLW context condition
        (compileProgExactHOLW context thenBranch)
        (compileProgExactHOLW context elseBranch)
  | .while condition body =>
      compileWhileExactHOLW context condition (compileProgExactHOLW context body)
  | .break => .break 0
  | .continue => .continue 0
  | .call info function arguments =>
      match info with
      | none => compileCallNoReturnExactHOLW context function arguments
      | some (none, none) =>
          compileCallResultNoHandlerExactHOLW context function arguments
      | some (none, some (exceptionName, exceptionVariable, body)) =>
          match hEid : context.eids.lookup exceptionName with
          | none =>
              compileCallHandlerMissingEidExactHOLW context function arguments
                exceptionName exceptionVariable body hEid
          | some exceptionCode =>
              compileCallHandlerPresentEidExactHOLW context function arguments
                exceptionName exceptionVariable exceptionCode hEid
                (fun bodyContext => compileProgExactHOLW bodyContext body)
      | some (some (_resultKind, resultName), handler) =>
          match hWrap : wrapRtHOL (context.vars.lookup resultName) with
          | none =>
              match handler with
              | none =>
                  compileCallWrappedResultFallbackNoHandlerExactHOLW context
                    function resultName arguments hWrap
              | some (exceptionName, exceptionVariable, body) =>
                  match hEid : context.eids.lookup exceptionName with
                  | none =>
                      compileCallWrappedResultFallbackHandlerMissingEidExactHOLW
                        context function resultName arguments exceptionName
                        exceptionVariable body hWrap hEid
                  | some exceptionCode =>
                      compileCallWrappedResultFallbackHandlerPresentEidExactHOLW
                        context function resultName arguments exceptionName
                        exceptionVariable exceptionCode hWrap hEid
                        (fun bodyContext => compileProgExactHOLW bodyContext body)
          | some (resultShape, resultNames) =>
              match handler with
              | none =>
                  compileCallWrappedResultNoHandlerExactHOLW context function
                    resultName arguments resultShape resultNames hWrap
              | some (exceptionName, exceptionVariable, body) =>
                  match hEid : context.eids.lookup exceptionName with
                  | none =>
                      compileCallWrappedResultHandlerMissingEidExactHOLW context
                        function resultName arguments resultShape resultNames
                        exceptionName exceptionVariable body hWrap hEid
                  | some exceptionCode =>
                      compileCallWrappedResultHandlerPresentEidExactHOLW context
                        function resultName arguments resultShape resultNames
                        exceptionName exceptionVariable exceptionCode hWrap hEid
                        (fun bodyContext => compileProgExactHOLW bodyContext body)
  | .decCall name shape function arguments body =>
      compileDecCallExactHOLW context name shape function arguments
        (fun bodyContext => compileProgExactHOLW bodyContext body)
  | .extCall function configuration configurationLength array arrayLength =>
      compileExtCallExactHOLW context function configuration configurationLength
        array arrayLength
  | .raise exceptionName expression =>
      compileRaiseExactHOLW context exceptionName expression
  | .return expression => compileReturnExactHOLW context expression
  | .shMemLoad operator .local name address =>
      compileShMemLoadExactHOLW context operator name address
  | .shMemLoad operator .global name address =>
      compileGlobalShMemLoadExactHOLW context operator name address
  | .shMemStore operator value address =>
      compileShMemStoreExactHOLW context operator value address
  | .tick => .tick
  | .annot _ _ => .skip
termination_by program => sizeOf program
decreasing_by
  all_goals
    simp_wf
    omega

/-! Exact HOL `comp_func_def` (`pan_to_crepScript.sml:337-343`). The four
curried arguments, the `make_vmap` result, the parameter-shape maximum, the
`mk_ctxt` field order, and recursive `compile` call follow the source
definition directly. The two input maps are the canonical finite-support
rendering of HOL `fs` and `eids`; `BitVec width` with `[NeZero width]` is the
usual positive type-indexed HOL word translation. Names and syntax stay on the
exact `MlS`/`ShapeHOL`/`ProgHOL`/`CrepProgHOL` carriers. The parser-backed
`compileProgTopHOLProductionExact` route calls this tagged wrapper; its
byte-ranged production context/parameter bridge and output-preservation proof
are recorded beside that route in `CompileProg.lean` under
`flapjack-pxn.18.3.5.8.25`. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "comp_func_def"
  (fmap_as_finite_support_relation := [fs, eids])
  (words_as_type_indexed_bitvec)]
def compFuncExactHOLW {width : Nat} [NeZero width]
    (fs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (eids : HolFiniteMapExact MlS (BitVec width))
    (params : List (MlS × ShapeHOL))
    (body : Flapjack.Pancake.PanLang.ProgHOL width) : CrepProgHOL width :=
  let vmap := panToCrepMakeVmapHOLExact params
  let shapes := params.map Prod.snd
  let vmax := sizeOfShapeHOL (.comb shapes) - 1
  compileProgExactHOLW (mkCtxtExactHOL vmap fs vmax eids) body

/-! ### Exact declaration-only `compile_to_crep_def`

This is the HOL pan_to_crepScript.sml:383-391 definition over
`List (DeclHOL width)`: project functions in source order, build the function
and exception-code maps from the original declarations, then emit one
`(name, crep_vars params, comp params body)` triple per projected function.
`makeFuncsExactHOL`, `getEidsFromDeclsHOL`, `functionsHOL`, `crepVarsHOL`, and
`compFuncExactHOLW` are the already reviewed tagged dependencies. The
finite-map values are local intermediates and do not occur in this
declaration's input or output type, so no finite-map carrier qualifier applies
here; their individual definition tags record their own result translations.
The only outer type translation is HOL's positive type-indexed word to
`BitVec width`. The production String-backed `compileToCrepHOL` route is still
separate; routing the executable compiler through this exact declaration-only
definition remains tracked by `flapjack-pxn.18.3.1.3`, and the exact
`compile_prog` boundary by `flapjack-4ac.2.20.2`. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_to_crep_def"
  (words_as_type_indexed_bitvec)]
def compileToCrepExactHOLW {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) :
    List (MlS × List Nat × CrepProgHOL width) :=
  let prog := functionsHOL declarations
  let fs := makeFuncsExactHOL prog
  let eids := getEidsFromDeclsHOL declarations
  prog.map (fun entry =>
    (entry.1, crepVarsHOL entry.2.1,
      compFuncExactHOLW fs eids entry.2.1 entry.2.2.1))


/-! ### Codec helper lemmas for the `compile_exp` production bridge

These untagged Flapjack lemmas are the list-level helpers needed to relate the
tagged exact `compileExpExactHOLW` (over `ExpHOL`/`CrepExpHOL`) to the executed
production `compileExpHOL` under the checked codecs `crepExpToHOL` and
`shapeToHOL`. They are part of the exact `code_rel` boundary work tracked by
`flapjack-pxn.18.4.3.73.1`. -/

/-- `cexpHeads` commutes with the element codec `crepExpToHOL`: taking heads of
    a list of expression lists and then decoding is the same as decoding each
    list first. -/
theorem cexpHeads_map_crepExpToHOL {width : Nat} [NeZero width]
    (lists : List (List (CrepExp (BitVec width)))) :
    cexpHeads (lists.map (List.map crepExpToHOL)) =
      (cexpHeads lists).map (List.map crepExpToHOL) := by
  induction lists with
  | nil => rfl
  | cons expressions rest ih =>
      cases expressions with
      | nil =>
          simp only [List.map_cons, List.map_nil, cexpHeads]
          rfl
      | cons expression expressions =>
          cases h : cexpHeads rest with
          | none =>
              simp only [List.map_cons, cexpHeads, ih, h]
              rfl
          | some heads =>
              simp only [List.map_cons, cexpHeads, ih, h]
              rfl

/-- Production-to-exact direction of HOL `crepLang$load_shape_def`: the
    width-indexed production loader `loadShapeBytes` decodes into the tagged
    exact `loadShapeBytesHOLW`. Dual to `loadShapeBytesHOLW_toProduction`. -/
theorem loadShapeBytes_map_crepExpToHOL {width : Nat} [NeZero width]
    (address : BitVec width) (count : Nat) (value : CrepExp (BitVec width)) :
    (loadShapeBytes address count value).map crepExpToHOL =
      loadShapeBytesHOLW address count (crepExpToHOL value) := by
  induction count generalizing address with
  | zero => simp [loadShapeBytesHOLW, loadShapeBytes]
  | succ count ih =>
      simp only [loadShapeBytesHOLW, loadShapeBytes, List.map_cons]
      rw [ih]
      congr 1
      simp only [beq_iff_eq]
      by_cases hzero : address = 0
      · rw [if_pos hzero, if_pos hzero]
        simp [crepExpToHOL]
      · rw [if_neg hzero, if_neg hzero]
        simp [crepExpToHOL]

/-- The `loadShapeBytesW` corollary used by the width-indexed compiler path. -/
theorem loadShapeBytesW_map_crepExpToHOL {width : Nat} [NeZero width]
    (address : BitVec width) (count : Nat) (value : CrepExp (BitVec width)) :
    (loadShapeBytesW address count value).map crepExpToHOL =
      loadShapeBytesHOLW address count (crepExpToHOL value) :=
  loadShapeBytes_map_crepExpToHOL address count value

/-- HOL `compile_prog_def`: extract inlineable function names from the original
ordered declarations, compile every function to exact Crep, then inline the
selected names. Both input and output use the reviewed exact carriers; only
HOL's positive type-indexed word is translated to `BitVec width`.

The canonical inline wrapper derives its finite-support certificate from the
filtered alist. Its unconditional theorem
`compileInlTopHOLExact_eq_compileInlProgHOLExact` identifies this computable
implementation with the source-shaped wrapper using `inlineProgHOLExact`.
No certificate or successful-pass premise is added to this declaration.

This is the exact declaration-level compiler, separate from the executed
production carrier bridge. That remaining route is tracked by
`flapjack-4ac.2.20.3` and `flapjack-e7w.2`; tagging this definition does not
establish that production route. -/
@[hol "cakeml/pancake/pan_to_crepScript.sml" "compile_prog_def"
  (words_as_type_indexed_bitvec)]
def compileProgDeclsHOLW {width : Nat} [NeZero width]
    (prog : List (DeclHOL width)) :
    List (MlS × List Nat × CrepProgHOL width) :=
  let inl_fs_names := (functionsHOL (prog.filter inlinableHOL)).map Prod.fst
  let to_crep := compileToCrepExactHOLW prog
  CrepInlineCanonical.compileInlTopHOLExact inl_fs_names to_crep

/-- Exact port of HALF of HOL `compile_prog_distinct_params`
    (`pan_to_crepProofScript.sml:4684-4691`): every parameter list produced by
    the exact `compile_to_crep` is `Nodup`.  HOL derives this from
    `crep_vars_def` (`GENLIST I (size_of_shape (Comb (MAP SND params)))`) and
    `ALL_DISTINCT_GENLIST`; on the exact carriers `crepVarsHOL params` is
    `List.range (sizeOfShapeHOL (.comb (params.map Prod.snd)))`, which is
    `Nodup`.  Untagged Flapjack infrastructure (bead
    `flapjack-4ac.2.20.1.1`). -/
theorem compileToCrepExactHOLW_params_nodup {width : Nat} [NeZero width]
    (declarations : List (DeclHOL width)) :
    (compileToCrepExactHOLW declarations).all
      (fun triple => triple.2.1.Nodup) = true := by
  unfold compileToCrepExactHOLW
  simp only [List.all_map]
  apply List.all_eq_true.mpr
  intro entry _
  simp only [crepVarsHOL]
  exact decide_eq_true List.nodup_range

/-- The canonical inline pass `compileInlProgHOLExactWithSupport` preserves the
    parameter component of every triple (definitionally, by the `MAP` over
    triples), so it preserves parameter distinctness.  This is the second half
    of HOL `compile_prog_distinct_params`. -/
theorem compileInlProgHOLExactWithSupport_params_nodup {width : Nat} [NeZero width]
    [BEq CrepInlineMapHOLName] [LawfulBEq CrepInlineMapHOLName]
    (inl_fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (supportKeys : List CrepInlineMapHOLName)
    (support_spec : ∀ key, inl_fs.lookup key ≠ none → key ∈ supportKeys)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    (CrepInlineCanonical.compileInlProgHOLExactWithSupport inl_fs supportKeys
        support_spec prog).all (fun triple => triple.2.1.Nodup) =
      prog.all (fun triple => triple.2.1.Nodup) := by
  unfold CrepInlineCanonical.compileInlProgHOLExactWithSupport
  simp only [List.all_map]
  rfl

/-- Exact port of HOL `compile_prog_distinct_params`
    (`pan_to_crepProofScript.sml:4684-4691`): every parameter list in the
    `compile_prog` output is `Nodup`.  Follows from the `compile_to_crep` half
    (`compileToCrepExactHOLW_params_nodup`) and definitional parameter
    preservation by the inline pass.  Untagged until the recursive inline core
    `flapjack-e7w.2.1.13` is reviewed. -/
theorem compileProgDeclsHOLW_params_nodup {width : Nat} [NeZero width]
    (prog : List (DeclHOL width)) :
    (compileProgDeclsHOLW prog).all (fun triple => triple.2.1.Nodup) = true := by
  unfold compileProgDeclsHOLW
  simp only [CrepInlineCanonical.compileInlTopHOLExact,
    CrepInlineCanonical.compileInlProgHOLExactWithSupport, List.all_map]
  exact compileToCrepExactHOLW_params_nodup prog

end Flapjack

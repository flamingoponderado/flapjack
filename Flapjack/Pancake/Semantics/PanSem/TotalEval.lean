import Flapjack.Pancake.Semantics.PanSem.TotalSteps
import Flapjack.Pancake.Semantics.PanSem.TotalMeasure
import Flapjack.Pancake.Semantics.PanSem.LookupCode

/-!
# Measured total `panSem$evaluate` over the production `Prog`/`PanSemState`

This module assembles the HOL-shaped result/state clause steps already landed in
`PanSem/TotalSteps.lean` (and the clock-leaf equations of `PanSem/Total.lean`)
into a single **total, recursive** evaluator

```
panSemTotalEvaluate primitive : Prog (RiscV.Word 64) →
  PanSemState (RiscV.Word 64) (FfiState σ) →
    Option (PanSemHOLResult (RiscV.Word 64)) ×
      PanSemState (RiscV.Word 64) (FfiState σ)
```

over the *full production* `Prog` syntax and the *complete* production
`PanSemState` (locals/globals/structs/code/exception shapes/memory/memaddrs/
sharedMemaddrs/clock/be/ffi/base/top).  It dispatches **every** production
constructor: `Skip`, `Dec`, `Assign`, `Primitive`, `Store`, `Store32`,
`StoreByte`, `Seq`, `If`, `While`, `Break`, `Continue`, `Call`, `DecCall`,
`ExtCall`, `Raise`, `Return`, `ShMemLoad`, `ShMemStore`, `Tick`, `Annot`.

Recursion is justified by the well-founded lexicographic measure
`panSemEvalMeasure state program = (state.clock, panSemProgFuel program)`
(`PanSem/TotalMeasure.lean`), never by an externally supplied fuel argument or
a caller-provided recursive callback:

* `Seq` and `If` recurse on their source subprograms at the same clock (the
  `Seq` continuation runs after `panSemFixClock`, which cannot raise the clock);
* `Dec` recurses on its body at the same clock;
* `While`, `Call`, and `DecCall` recurse at the HOL-decremented clock
  (`state.clock - 1`), and `Call`/`DecCall` resolve the callee body and fresh
  locals from the *state-owned* finite code map (`state.code` via
  `lookupPanSemCodeCall`), so the evaluator carries no detached function table.

## Constructors that reuse the landed clause steps

The non-recursive and fixed-subprogram clauses are the reviewed helpers, so the
executed equations stay in one place:

* `Skip`/`Break`/`Continue`/`Tick` use `panSemEvaluateClockLeaf`;
* `Assign`, `Primitive`, `Store`, `Store32`, `StoreByte`, `Raise`, `Return`,
  `ShMemLoad`, `ShMemStore`, `ExtCall` use the eponymous `panSemTotal*Clause`
  helpers.
* `Annot` is erased to `(none, state)`, exactly the body of
  `panSemTotalAnnotClause` (the helper fixes `α` and `σ` to the same universe,
  so it is not applied at the fixed `RiscV.Word 64`/`σ` carriers here).

The genuinely recursive clauses are written out here rather than routed through
`panSemTotalDecClause`, `panSemTotalIfStep`, `panSemTotalWhileStep`,
`panSemTotalCallStep`, or `panSemTotalDecCallStep`.  Those helpers take their
recursive continuation as an *abstract* `PanSemState → …` callback; passing this
evaluator as that callback would hide the next state from the termination
checker, whose first measure coordinate is `state.clock`.  The bodies below
follow those helpers clause-for-clause (including the `panSemFixClock` clamp,
the `panEmptyLocals` timeout/return handling, and the `resVar` restoration), and
`Flapjack/Test/PanSemTotalEvalParity.lean` pins the resulting behavior against
the original HOL probe rows for the recursive `Call`/`DecCall` cases.

## Exact `eval_def` boundary (kept explicit)

This is an **untagged** Flapjack evaluator, *not* the HOL `evaluate_def` port.
Production names are Lean `String` while HOL's `varname`/`funname` are
`mlstring`, and the executed expression evaluator `evalPanSemStateExp` has only
an executed-path agreement with the untagged `evalHOL`, not the exact
`evalHOLExact` over the `ProgHOL`/`ExpHOL`/`PanSemStateExact` carrier
(`PanSem/EvalExact.lean`, `PanSem/TotalEvalExact.lean`).  The kernel-checked
carrier bridge is `PanSem/StateBridge.lean`.  No `@[hol]` tag is claimed until
the full statement and the expression carrier are exact; the remaining exact
`eval_def` dependency is tracked by `flapjack-pxn.18.4.3.77.2` and its exact
child slices.  Nothing here routes an unsupported branch to `Error`: every
production constructor is dispatched by its HOL clause.
-/

namespace Flapjack

variable {σ : Type v}

/-- Convert the state-owned `lookup_code` result into the argument order used by
    the recursive `Call`/`DecCall` clause bodies: body, freshly bound callee
    locals, and declared return shape.  The callee is resolved from
    `state.code` (never a detached table), and a missing, duplicate-named, or
    shape-mismatched callee yields `none`, matching HOL `lookup_code`. -/
def panSemTotalCodeLookup [BEq String]
    (state : PanSemState (RiscV.Word 64) (FfiState σ))
    (function : FunName) (arguments : List (PanValue (RiscV.Word 64))) :
    Option (Prog (RiscV.Word 64) ×
      (VarName → Option (PanValue (RiscV.Word 64))) × Shape) :=
  match lookupPanSemCodeCall state.structs state.code function arguments with
  | none => none
  | some (body, returnShape, locals) => some (body, locals, returnShape)

/-- Total, well-founded recursive `panSem$evaluate` over the complete production
    RISC-V 64-bit `Prog` syntax and `PanSemState`.  The result is HOL's
    `result option` (`none` is normal completion) paired with the final state;
    the `Option` is the semantic result option, not an evaluator-fuel wrapper.

    `If`/`Seq`/`Dec` recurse on source subprograms under `panSemEvalMeasure`;
    `While`/`Call`/`DecCall` recurse at `state.clock - 1`; `Call`/`DecCall`
    bodies come from `state.code`.  The definition is intentionally untagged:
    see the module docs for the `String`/exact-`eval_def` carrier boundary. -/
def panSemTotalEvaluate [NeZero 64]
    [BEq (RiscV.Word 64)] [DecidableEq (RiscV.Word 64)]
    [OfNat (RiscV.Word 64) 0] [OfNat (RiscV.Word 64) 1]
    [OfNat (RiscV.Word 64) 2] [OfNat (RiscV.Word 64) 3]
    [Add (RiscV.Word 64)] [Mul (RiscV.Word 64)] [Sub (RiscV.Word 64)]
    [AndOp (RiscV.Word 64)] [OrOp (RiscV.Word 64)]
    [HXor (RiscV.Word 64) (RiscV.Word 64) (RiscV.Word 64)]
    [ShiftLeft (RiscV.Word 64)] [ShiftRight (RiscV.Word 64)]
    [LT (RiscV.Word 64)]
    [DecidableRel (fun left right : RiscV.Word 64 => left < right)]
    [PanCmp (RiscV.Word 64)] [BEq String] [LawfulBEq String]
    (primitive : PanPrimitiveHandler (RiscV.Word 64)) :
    Prog (RiscV.Word 64) →
      PanSemState (RiscV.Word 64) (FfiState σ) →
        Option (PanSemHOLResult (RiscV.Word 64)) ×
          PanSemState (RiscV.Word 64) (FfiState σ)
  | .skip, state => panSemEvaluateClockLeaf .skip state
  | .break, state => panSemEvaluateClockLeaf .break state
  | .continue, state => panSemEvaluateClockLeaf .continue state
  | .tick, state => panSemEvaluateClockLeaf .tick state
  | .assign kind name value, state =>
      panSemTotalAssignClause state kind name value
  | .primitive name operator arguments, state =>
      panSemTotalPrimitiveClause state name operator arguments primitive
  | .store address value, state => panSemTotalStoreClause state address value
  | .store32 address value, state => panSemTotalStore32Clause state address value
  | .storeByte address value, state => panSemTotalStoreByteClause state address value
  | .raise exception value, state => panSemTotalRaiseClause state exception value
  | .return value, state => panSemTotalReturnClause state value
  | .annot _tag _text, state => (none, state)
  | .dec name shape value body, state =>
      match evalPanSemStateExp state value with
      | none => (some .error, state)
      | some evaluated =>
          if panShapeMatches shape (panSemShapeOf evaluated) then
            let bodyState := panSemTotalDecBind state name evaluated
            let bodyResult := panSemTotalEvaluate primitive body bodyState
            (bodyResult.1, { bodyResult.2 with
              locals := resVar bodyResult.2.locals (name, state.locals name) })
          else (some .error, state)
  | .seq first second, state =>
      let firstResult := panSemTotalEvaluate primitive first state
      let fixedState := panSemFixClock state.clock firstResult.2
      match firstResult.1 with
      | none => panSemTotalEvaluate primitive second fixedState
      | some result => (some result, fixedState)
  | .ite condition thenBranch elseBranch, state =>
      match evalPanSemStateExp state condition with
      | some (.word value) =>
          if value = 0 then panSemTotalEvaluate primitive elseBranch state
          else panSemTotalEvaluate primitive thenBranch state
      | _ => (some .error, state)
  | .while condition body, state =>
      match evalPanSemStateExp state condition with
      | some (.word value) =>
          if value = 0 then (none, state)
          else if state.clock = 0 then (some .timeOut, panEmptyLocals state)
          else
            let decState := { state with clock := state.clock - 1 }
            let bodyResult := panSemTotalEvaluate primitive body decState
            let fixedState := panSemFixClock decState.clock bodyResult.2
            match bodyResult.1 with
            | none => panSemTotalEvaluate primitive (.while condition body) fixedState
            | some .continue =>
                panSemTotalEvaluate primitive (.while condition body) fixedState
            | some .break => (none, fixedState)
            | other => (other, fixedState)
      | _ => (some .error, state)
  | .call info function arguments, state =>
      match evalPanSemStateExps state arguments with
      | none => (some .error, state)
      | some values =>
          match panSemTotalCodeLookup state function values with
          | none => (some .error, state)
          | some (callee, newLocals, returnShape) =>
              if state.clock = 0 then (some .timeOut, panEmptyLocals state)
              else
                let entry := { state with
                  clock := state.clock - 1
                  locals := newLocals }
                let bodyResult := panSemTotalEvaluate primitive callee entry
                let fixedState := panSemFixClock entry.clock bodyResult.2
                match bodyResult.1 with
                | none | some .break | some .continue => (some .error, fixedState)
                | some (.returned value) =>
                    if panShapeMatches (panSemShapeOf value) returnShape then
                      match info with
                      | none => (some (.returned value), panEmptyLocals fixedState)
                      | some (none, _) =>
                          (none, { fixedState with locals := state.locals })
                      | some (some (kind, name), _) =>
                          if panValueAssignmentValid state.structs state.locals
                              state.globals kind name value then
                            (none, match kind with
                              | .local => { fixedState with
                                  locals := updatePanValueMap state.locals name value }
                              | .global => { fixedState with
                                  locals := state.locals
                                  globals := updatePanValueMap fixedState.globals name value })
                          else (some .error, fixedState)
                    else (some .error, fixedState)
                | some (.exception exceptionId value) =>
                    match info with
                    | none => (some (.exception exceptionId value), panEmptyLocals fixedState)
                    | some (_, none) =>
                        (some (.exception exceptionId value), panEmptyLocals fixedState)
                    | some (_, some (handlerId, handlerVar, handlerProg)) =>
                        if exceptionId == handlerId then
                          match state.exceptionShapes exceptionId with
                          | some shape =>
                              if panShapeMatches (panSemShapeOf value) shape &&
                                  panValueAssignmentValid state.structs state.locals
                                    state.globals .local handlerVar value then
                                panSemTotalEvaluate primitive handlerProg
                                  { fixedState with locals :=
                                    updatePanValueMap state.locals handlerVar value }
                              else (some .error, fixedState)
                          | none => (some .error, fixedState)
                        else
                          (some (.exception exceptionId value), panEmptyLocals fixedState)
                | some other => (some other, panEmptyLocals fixedState)
  | .decCall name shape function arguments continuation, state =>
      match evalPanSemStateExps state arguments with
      | none => (some .error, state)
      | some values =>
          match panSemTotalCodeLookup state function values with
          | none => (some .error, state)
          | some (callee, newLocals, returnShape) =>
              if state.clock = 0 then (some .timeOut, panEmptyLocals state)
              else
                let entry := { state with
                  clock := state.clock - 1
                  locals := newLocals }
                let bodyResult := panSemTotalEvaluate primitive callee entry
                let fixedState := panSemFixClock entry.clock bodyResult.2
                match bodyResult.1 with
                | none | some .break | some .continue => (some .error, fixedState)
                | some (.returned value) =>
                    if panShapeMatches shape (panSemShapeOf value) &&
                        panShapeMatches shape returnShape then
                      let bound := { fixedState with
                        locals := updatePanValueMap state.locals name value }
                      let continuationResult :=
                        panSemTotalEvaluate primitive continuation bound
                      (continuationResult.1,
                        { continuationResult.2 with
                          locals := resVar continuationResult.2.locals
                            (name, state.locals name) })
                    else (some .error, fixedState)
                | some other => (some other, panEmptyLocals fixedState)
  | .extCall function configuration configurationLength array arrayLength, state =>
      panSemTotalExtCallClause state function configuration configurationLength array arrayLength
  | .shMemLoad size kind name address, state =>
      panSemTotalShMemLoadClause state size kind name address
  | .shMemStore size address value, state =>
      panSemTotalShMemStoreClause state size address value
termination_by program state => panSemEvalMeasure state program
decreasing_by
  all_goals
    simp_wf
    simp [panSemEvalMeasure, panSemProgFuel, panSemFixClock,
      panSemTotalDecBind]
    omega

end Flapjack

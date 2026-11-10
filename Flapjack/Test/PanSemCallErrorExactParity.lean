module

public import Flapjack.Pancake.Semantics.PanSemStateEval
public import Flapjack.Test.PanValueFfiCore

-- Checks below run compiled code from these modules.
public meta import Flapjack.Test.PanValueFfiCore
public meta import Flapjack.Pancake.Semantics.PanSemStateEval
@[expose] public section

-- Public declarations below use private helpers.
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
Direct regression for the source `PanSemState` code-map `Call` error
equations.  HOL evaluates the argument list with `OPT_MMAP (eval s) argexps`
before the callee lookup, so a memory-reading argument is gated by the source
`memaddrs`: an address outside the domain rejects the call with `SOME Error`
over the unchanged state, even when the raw memory function holds a cell.  An
unknown callee is likewise rejected.  The expected values are the original-HOL
`EVAL` rows in `scripts/hol-probes/pan_sem_call_error_state_probe.out`.
The return-shape conflict case is paired with
`pan_sem_call_return_shape_probe.out`: HOL accepts `goodret` because its
`state.code` entry declares `One`; the mismatched source code-map row returns
`Error`.

* `call_error_load_result=SOME Error`, `call_error_load_clock=5`,
  `call_error_load_locals=SOME (ValWord 3w)`;
* `call_error_domain_result=SOME Error`,
  `call_error_domain_locals=SOME (ValWord 3w)`;
* `call_error_missing_result=SOME Error`, `call_error_missing_clock=5`.

This module is untagged infrastructure: the reduced `PanValueFfiClockResult`
encoding is not literally HOL's `(result option # state)` type, so no `@[hol]`
attribute is attached.
-/

namespace Flapjack.Test.PanSemCallErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- Source memory with a present word cell at address `8` and a zero fallback. -/
private def exactMemory : Word64 → Option (PanValue Word64) :=
  fun address =>
    if address == 8 then some (.word (BitVec.ofNat 64 0x77)) else some (.word 0)

private def exactDomain : Word64 → Bool :=
  fun address => address == 8

/-- A domain that misses every address, so every source read fails. -/
private def emptyDomain : Word64 → Bool := fun _ => false

private def localsWithX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

private def callerLocalX : VarName -> Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

/-- State-owned source state: source locals, memory, `memaddrs` domain, and a
    state-owned code map.  The exception shape map is empty. -/
private def sourceState (clock : Nat) (locals : VarName → Option (PanValue Word64))
    (memory : Word64 → Option (PanValue Word64)) (domain : Word64 → Bool)
    (code : PanSemCodeMap Word64) : PanSemState Word64 (FfiState Unit) :=
  { locals := locals
    globals := fun _ => none
    structs := []
    code := code
    exceptionShapes := fun _ => none
    memory := memory
    memaddrs := domain
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

private def evaluate (state : PanSemState Word64 (FfiState Unit)) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

private def isWordValue (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

private def isErrorKeeping (clock localValue : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ => n == clock && isWordValue localValue (locals "x")
      | _ => false
  | _ => false

private def loadHit : Exp Word64 := .load Shape.one (.const 8)

private def loadMiss : Exp Word64 := .load Shape.one (.const 11)

private def missingCall : Prog Word64 := .call none "f" [.const 1]

/-- State with a present memory cell at address `8` and local `x`. -/
private def memoryState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 localsWithX exactMemory exactDomain []

/-- State whose `memaddrs` domain is empty while the raw memory holds a cell. -/
private def emptyDomainState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 localsWithX exactMemory emptyDomain []

/-- State whose source evaluation fails immediately (no locals, no memory). -/
private def emptyState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 (fun _ => none) (fun _ => none) emptyDomain []

/-- State whose `Const` evaluation succeeds. -/
private def wordState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 (fun _ => some (.word 7)) (fun _ => none) exactDomain []

/-- State with a one-parameter callee `f`. -/
private def parameterState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 (fun _ => some (.word 7)) (fun _ => none) exactDomain
    [("f", ([("p", Shape.one)], .skip, Shape.one))]

/-- HOL-oracle-constant parity fixture.  The checked-in probe
    `scripts/hol-probes/pan_sem_call_arity_probe.out` runs both mismatches at
    `clock := 5` with local `x = ValWord 3w`; this state uses those exact
    constants so the Lean guards pair row-for-row with the HOL `EVAL` output. -/
private def oracleParameterState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 localsWithX (fun _ => none) exactDomain
    [("f", ([("p", Shape.one)], .skip, Shape.one))]

/-- Result matcher for the callee-fallthrough rejection, pairing all four rows
    of `scripts/hol-probes/pan_sem_call_callee_normal_probe.out`: an `Error` at
    the decremented callee clock, whose `p` local still holds the bound
    argument and whose caller's `x` local is absent (the result carries the
    callee's post-call state, whose locals hold only the bound parameters). -/
private def isFallThroughError (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock && (match locals "p" with
            | some (.word w) => w == BitVec.ofNat 64 value
            | _ => false) && (locals "x").isNone
      | _ => false
  | _ => false

/-- State whose callee `f` has body `Skip` and therefore falls through. -/
private def fallThroughState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 (fun _ => some (.word 3)) (fun _ => none) exactDomain
    [("f", ([("p", Shape.one)], .skip, Shape.one))]

private def callFallThroughGuard : Bool :=
  isFallThroughError 4 1 (evaluate fallThroughState (.call none "f" [.const 1]))

/-- Result matcher for a callee that finishes with `Continue`: an `Error` at the
    decremented callee clock whose `p` local holds the bound argument and whose
    caller-local view (`x`) is empty. The `Break` counterpart is
    `isTerminalBreakError`; both pair with the corresponding HOL oracle rows. -/
private def isTerminalError (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock && (locals "x").isNone && (match locals "p" with
            | some (.word w) => w == BitVec.ofNat 64 value
            | _ => false)
      | _ => false
  | _ => false

private def breakState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 callerLocalX (fun _ => none) exactDomain
    [("f", ([("p", Shape.one)], .break, Shape.one))]

private def continueState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 callerLocalX (fun _ => none) exactDomain
    [("f", ([("p", Shape.one)], .continue, Shape.one))]

/-- Break-specific matcher pairing all four rows of
    `scripts/hol-probes/pan_sem_call_callee_terminal_probe.out`: the fourth row
    `call_break_caller_locals=NONE` requires the caller's `x` local to be absent
    in the callee post-state, in addition to the `Error`/`p`/clock rows shared
    with `isTerminalError`. -/
private def isTerminalBreakError (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock && (match locals "p" with
            | some (.word w) => w == BitVec.ofNat 64 value
            | _ => false) && (locals "x").isNone
      | _ => false
  | _ => false

private def callBreakGuard : Bool :=
  isTerminalBreakError 4 1 (evaluate breakState (.call none "f" [.const 1]))

private def callContinueGuard : Bool :=
  isTerminalError 4 1 (evaluate continueState (.call none "f" [.const 1]))

/-- Result matcher for a callee that finishes with `Error`: the call propagates
    `SOME Error` through the catch-all `empty_locals st`, so the caller-visible
    locals are cleared at the decremented callee clock. -/
private def isPropagatedError (clock : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock && (locals "p").isNone && (locals "x").isNone
      | _ => false
  | _ => false

/-- State whose callee `f` errors while evaluating its body: it reads address
    `11` outside the domain, so the callee finishes with `Error`. -/
private def calleeErrorState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 (fun _ => some (.word 3)) (fun _ => none) exactDomain
    [("f", ([("p", Shape.one)], .assign .local "p" (.load Shape.one (.const 11)), Shape.one))]

private def callCalleeErrorGuard : Bool :=
  isPropagatedError 4 (evaluate calleeErrorState (.call none "f" [.const 1]))

/-- The `goodret` fixture of `pan_sem_call_return_shape_probe.out`: the source
    code entry declares `One`, so HOL accepts the returned word. -/
private def goodReturnState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 (fun _ => some (.word 3)) (fun _ => none) exactDomain
    [("f", ([("p", Shape.one)], .return (.const 0), Shape.one))]

private def callReturnShapeAcceptGuard : Bool :=
  match evaluate goodReturnState (.call none "f" [.const 1]) with
  | some (.control (.returned _ _ _ _ [.word value]), clock) =>
      clock == 4 && value == BitVec.ofNat 64 0
  | _ => false

private def callLoadMissGuard : Bool :=
  isErrorKeeping 5 3 (evaluate memoryState (.call none "f" [loadMiss]))

private def callParamArityGuard : Bool :=
  isErrorKeeping 5 7 (evaluate parameterState (.call none "f" []))

private def callParamShapeGuard : Bool :=
  isErrorKeeping 5 7 (evaluate parameterState (.call none "f" [.rStruct []]))

/-- Oracle-row parity for `call_arity_miss_result`/`call_arity_miss_locals`/
    `call_arity_miss_clock`. -/
private def oracleArityGuard : Bool :=
  isErrorKeeping 5 3 (evaluate oracleParameterState (.call none "f" []))

/-- Oracle-row parity for `call_arity_shape_miss_result`. -/
private def oracleShapeGuard : Bool :=
  isErrorKeeping 5 3 (evaluate oracleParameterState (.call none "f" [.rStruct []]))

private def callMissingGuard : Bool :=
  isErrorKeeping 5 3 (evaluate memoryState missingCall)

private def callDomainGuard : Bool :=
  isErrorKeeping 5 3 (evaluate emptyDomainState (.call none "f" [loadHit]))

private def callGuard : Bool :=
  callLoadMissGuard && callMissingGuard && callDomainGuard &&
    callParamArityGuard && callParamShapeGuard && oracleArityGuard && oracleShapeGuard &&
    callFallThroughGuard &&
    callBreakGuard && callContinueGuard && callCalleeErrorGuard &&
    callReturnShapeAcceptGuard

#guard callGuard

/-- A `Call` whose argument fails to evaluate returns `SOME Error` over the
    full source state. -/
theorem callArgsMiss_eq :
    evaluate emptyState (.call none "f" [.var .local "z"]) =
      some (.control (.error emptyState.locals emptyState.globals
        emptyState.memory emptyState.ffi), emptyState.clock) := by
  simp (config := { decide := true }) [evaluate, emptyState, sourceState,
    panSemEvaluateRiscV64CodeState, panSemEvaluateWordCodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemProgFuel,
    panSemExpFuel, panSemExpListFuel, panSemCodeBodyFuel, panSemCallInfoFuel,
    panSemBitVec64BytesInWord, evalPanValueFfiClockCodeProg,
    evalPanValueFfiClockCodeCall, panValueCallArgumentsValue, lookupPanSemCodeCall,
    panSemCodeLookup, lookupInfo, bindPanValueParameters, evalPanValueExps,
    evalPanValueExpsWith, evalPanValueExp.evalPanValueExps, evalPanValueExp]

/-- A `Call` naming an unknown callee returns `SOME Error` over the full source
    state. -/
theorem callMissing_eq :
    evaluate wordState missingCall =
      some (.control (.error wordState.locals wordState.globals
        wordState.memory wordState.ffi), wordState.clock) := by
  simp (config := { decide := true }) [evaluate, wordState, sourceState, missingCall,
    panSemEvaluateRiscV64CodeState, panSemEvaluateWordCodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemProgFuel,
    panSemExpFuel, panSemExpListFuel, panSemCodeBodyFuel, panSemCallInfoFuel,
    panSemBitVec64BytesInWord, evalPanValueFfiClockCodeProg,
    evalPanValueFfiClockCodeCall, panValueCallArgumentsValue, lookupPanSemCodeCall,
    panSemCodeLookup, lookupInfo, bindPanValueParameters, evalPanValueExps,
    evalPanValueExpsWith, evalPanValueExp.evalPanValueExps, evalPanValueExp]

/-- A `Call` whose argument list does not match the callee's parameter shapes
    returns `SOME Error` over the full source state. -/
theorem callParamArity_eq :
    evaluate parameterState (.call none "f" []) =
      some (.control (.error parameterState.locals parameterState.globals
        parameterState.memory parameterState.ffi),
        parameterState.clock) := by
  simp (config := { decide := true }) [evaluate, parameterState, sourceState,
    panSemEvaluateRiscV64CodeState, panSemEvaluateWordCodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemProgFuel,
    panSemExpListFuel, panSemCodeBodyFuel, panSemCallInfoFuel,
    panSemBitVec64BytesInWord, evalPanValueFfiClockCodeProg,
    evalPanValueFfiClockCodeCall, panValueCallArgumentsValue, lookupPanSemCodeCall,
    panSemCodeLookup, lookupInfo, bindPanValueParameters, evalPanValueExps,
    evalPanValueExpsWith, evalPanValueExp.evalPanValueExps]

/-- Source state with a state-owned code map, start clock 5, and a caller local
    `caller = 3`.  This exercises the code-map Call/DecCall path, which is where
    HOL's per-entry `returnShape` check lives. -/
private def badReturnShapeState (code : PanSemCodeMap Word64) :
    PanSemState Word64 (FfiState Unit) :=
  { locals := fun name => if name == "caller" then some (.word (BitVec.ofNat 64 3)) else none
    globals := fun _ => none
    structs := []
    code := code
    exceptionShapes := fun _ => none
    memory := fun _ => some (.word 0)
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

private def badReturnCode : PanSemCodeMap Word64 :=
  [("badret", ([], .return (.const (BitVec.ofNat 64 7)), .comb [.one, .one]))]

private def badReturnParamCode : PanSemCodeMap Word64 :=
  [("badret_param", ([("x", .one)], .return (.const (BitVec.ofNat 64 7)),
    .comb [.one, .one]))]

/-- A scoped declaration restores the callee's parameter after its body
    returns, so the subsequent return-shape error must keep that binding. -/
private def badReturnRestoredLocalCode : PanSemCodeMap Word64 :=
  [("badret_restored", ([("x", .one)],
    .dec "x" .one (.const 9) (.return (.const 7)), .comb [.one, .one]))]

private def goodReturnCode : PanSemCodeMap Word64 :=
  [("goodret", ([], .return (.const (BitVec.ofNat 64 7)), .one))]

/-- Source code entry matching `scripts/hol-probes/pan_sem_call_return_invalid_probe.out`:
    callee `f` binds one `One` parameter `p`, returns `0`, and declares the
    mismatching return shape `Named "Other"`. -/
private def invalidReturnCode : PanSemCodeMap Word64 :=
  [("f", ([("p", .one)], .return (.const (BitVec.ofNat 64 0)), .named "Other"))]

private def codeEvaluate (state : PanSemState Word64 (FfiState Unit))
    (program : Prog Word64) : Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

/-- `Error` at the decremented clock with no caller or parameter locals. -/
private def isBadReturnShapeError (clock : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock && (locals "caller").isNone && (locals "x").isNone
      | _ => false
  | _ => false

private def callBadReturnShapeGuard : Bool :=
  isBadReturnShapeError 4
    (codeEvaluate (badReturnShapeState badReturnCode) (.call none "badret" []))

private def callBadReturnShapeParamGuard : Bool :=
  isBadReturnShapeError 4
    (codeEvaluate (badReturnShapeState badReturnParamCode)
      (.call none "badret_param" [.const (BitVec.ofNat 64 4)]))

private def callBadReturnRestoredLocalGuard : Bool :=
  match codeEvaluate (badReturnShapeState badReturnRestoredLocalCode)
      (.call none "badret_restored" [.const (BitVec.ofNat 64 4)]) with
  | some (.control (.error locals _ _ _), clock) =>
      clock == 4 && isWordValue 4 (locals "x") && (locals "caller").isNone
  | _ => false

#guard callBadReturnRestoredLocalGuard

private def decCallBadReturnShapeGuard : Bool :=
  isBadReturnShapeError 4
    (codeEvaluate (badReturnShapeState badReturnCode)
      (.decCall "dest" .one "badret" [] .skip))

private def callGoodReturnShapeGuard : Bool :=
  match codeEvaluate (badReturnShapeState goodReturnCode) (.call none "goodret" []) with
  | some (.control (.returned _ _ _ _ [.word value]), n) =>
      n == 4 && value == BitVec.ofNat 64 7
  | _ => false

/-- Oracle-row matcher for `scripts/hol-probes/pan_sem_call_return_invalid_probe.out`:
    `SOME Error` at the decremented clock 4 with the callee parameter `p` and the
    caller local `caller` both absent. -/
private def isReturnInvalidError (clock : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ =>
          n == clock && (locals "p").isNone && (locals "caller").isNone
      | _ => false
  | _ => false

private def callInvalidReturnShapeGuard : Bool :=
  isReturnInvalidError 4
    (codeEvaluate (badReturnShapeState invalidReturnCode)
      (.call none "f" [.const (BitVec.ofNat 64 1)]))

/-- Kernel-checked code-map Call invalid-return-shape equation for the probe
    `badret` entry. -/
theorem callBadReturnShape_eq :
    codeEvaluate (badReturnShapeState badReturnCode) (.call none "badret" []) =
      some (.control (.error (fun _ => none) (fun _ => none)
        (fun _ => some (.word 0)) statefulTestFfiState), 4) := by
  have h := panSemEvaluateCodeState_call_error_of_returnShapeMismatch statefulTestContext
    statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8)
    (badReturnShapeState badReturnCode) "badret" (BitVec.ofNat 64 7)
    (by simp [badReturnShapeState, badReturnCode, panSemCodeLookup, lookupInfo])
    (by decide)
    (memoryAccess := some (panSemBitVec64MemoryAccess (badReturnShapeState badReturnCode)))
  simpa [codeEvaluate, panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    panSemBitVec64MemoryAccess, decPanClock,
    badReturnShapeState] using h

/-- Kernel-checked code-map Call invalid-return-shape equation for a callee with
    one parameter, whose binding is discarded on rejection. -/
theorem callBadReturnShapeParam_eq :
    codeEvaluate (badReturnShapeState badReturnParamCode)
      (.call none "badret_param" [.const (BitVec.ofNat 64 4)]) =
      some (.control (.error (fun _ => none) (fun _ => none)
        (fun _ => some (.word 0)) statefulTestFfiState), 4) := by
  have h := panSemEvaluateCodeState_call_error_of_returnShapeMismatch_param
    statefulTestContext statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8)
    (badReturnShapeState badReturnParamCode) "badret_param"
    (BitVec.ofNat 64 4) (BitVec.ofNat 64 7)
    (by simp [badReturnShapeState, badReturnParamCode, panSemCodeLookup, lookupInfo])
    (by decide)
    (memoryAccess := some
      (panSemBitVec64MemoryAccess (badReturnShapeState badReturnParamCode)))
  simpa [codeEvaluate, panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    panSemBitVec64MemoryAccess, decPanClock,
    badReturnShapeState] using h

/-- Kernel-checked code-map DecCall invalid-return-shape equation. -/
theorem decCallBadReturnShape_eq :
    codeEvaluate (badReturnShapeState badReturnCode)
      (.decCall "dest" .one "badret" [] .skip) =
      some (.control (.error (fun _ => none) (fun _ => none)
        (fun _ => some (.word 0)) statefulTestFfiState), 4) := by
  have h := panSemEvaluateCodeState_decCall_error_of_returnShapeMismatch
    statefulTestContext statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8)
    (badReturnShapeState badReturnCode) "dest" "badret" (BitVec.ofNat 64 7)
    (by simp [badReturnShapeState, badReturnCode, panSemCodeLookup, lookupInfo])
    (by decide)
    (memoryAccess := some (panSemBitVec64MemoryAccess (badReturnShapeState badReturnCode)))
  simpa [codeEvaluate, panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    panSemBitVec64MemoryAccess, decPanClock,
    badReturnShapeState] using h

/-- Kernel-checked code-map Call invalid-return-shape equation for the
    `scripts/hol-probes/pan_sem_call_return_invalid_probe.out` entry.  The
    returned `.word 0` mismatches the declared `Named "Other"` shape, so the call
    rejects with `SOME Error` at the decremented clock 4, with the callee
    parameter `p` and the caller local `caller` both absent.  It is proved from
    the generic callee-run-hypothesis equation
    `panSemEvaluateCodeState_call_error_of_callee_returnShapeMismatch`. -/
theorem callInvalidReturnShape_eq :
    codeEvaluate (badReturnShapeState invalidReturnCode)
      (.call none "f" [.const (BitVec.ofNat 64 1)]) =
      some (.control (.error (fun _ => none) (fun _ => none)
        (fun _ => some (.word 0)) statefulTestFfiState), 4) := by
  have h := panSemEvaluateCodeState_call_error_of_callee_returnShapeMismatch
    statefulTestContext statefulTestPrimitive statefulTestHandler (BitVec.ofNat 64 8)
    (badReturnShapeState invalidReturnCode) none "f"
    [.const (BitVec.ofNat 64 1)] [.word (BitVec.ofNat 64 1)]
    (.return (.const (BitVec.ofNat 64 0))) (.named "Other")
    (fun key => if key == "p" then some (.word (BitVec.ofNat 64 1)) else none)
    (fun _ => none) (fun _ => none) (fun _ => some (.word 0)) statefulTestFfiState
    (.word (BitVec.ofNat 64 0)) 4
    (panSemCodeEvaluateFuel (badReturnShapeState invalidReturnCode)
      (.call none "f" [.const (BitVec.ofNat 64 1)]) - 2)
    (memoryAccess := some (panSemBitVec64MemoryAccess (badReturnShapeState invalidReturnCode)))
    (contracts := none) (memoryHandler := none)
    (by simp [badReturnShapeState, invalidReturnCode, evalPanValueExps,
      evalPanValueExp.evalPanValueExps, evalPanValueExp, panSemBitVec64MemoryAccess])
    (by
      unfold lookupPanSemCodeCall
      simp [badReturnShapeState, invalidReturnCode, panSemCodeLookup, lookupInfo,
        panSemCodeArgumentsMatch, bindPanValueParameters, panValueShape,
        panShapeMatches]
      funext key
      simp [updatePanValueMap, beq_iff_eq])
    (by decide)
    (by
      have hval : panSemCodeEvaluateFuel (badReturnShapeState invalidReturnCode)
          (.call none "f" [.const (BitVec.ofNat 64 1)]) = 19 := by
        simp [panSemCodeEvaluateFuel, panSemProgFuel, panSemCodeBodyFuel,
          panSemExpListFuel, panSemExpFuel, panSemCallInfoFuel, badReturnShapeState,
          invalidReturnCode]
      omega)
    (by simp [badReturnShapeState, invalidReturnCode, evalPanValueFfiClockCodeProg,
      evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl, panValueReturnResult,
      evalPanValueExpWith, evalPanValueExp, panValuePayloadWithinLimit,
      panValuePayloadSize, decPanClock,
      panSemCodeEvaluateFuel, panSemProgFuel, panSemCodeBodyFuel,
      panSemExpListFuel, panSemExpFuel, panSemCallInfoFuel])
    (by simp [badReturnShapeState, invalidReturnCode, panValueShape, panShapeMatches])
  simpa [codeEvaluate, panSemEvaluateRiscV64CodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemBitVec64BytesInWord,
    panSemBitVec64MemoryAccess, decPanClock,
    badReturnShapeState] using h

private def stateCodeGuard : Bool :=
  callBadReturnShapeGuard && callBadReturnShapeParamGuard &&
    decCallBadReturnShapeGuard && callGoodReturnShapeGuard &&
    callInvalidReturnShapeGuard

#guard stateCodeGuard

def runChecks : IO Bool := do
  if callLoadMissGuard then
    IO.println "PASS source Call failing argument keeps state and clock"
  else IO.println "FAIL source Call failing argument keeps state and clock"
  if callMissingGuard then
    IO.println "PASS source Call unknown callee keeps state and clock"
  else IO.println "FAIL source Call unknown callee keeps state and clock"
  if callDomainGuard then
    IO.println "PASS source Call memory domain gates an argument read"
  else IO.println "FAIL source Call memory domain gates an argument read"
  if callParamArityGuard then
    IO.println "PASS source Call parameter arity mismatch keeps state and clock"
  else IO.println "FAIL source Call parameter arity mismatch keeps state and clock"
  if callParamShapeGuard then
    IO.println "PASS source Call parameter shape mismatch keeps state and clock"
  else IO.println "FAIL source Call parameter shape mismatch keeps state and clock"
  if oracleArityGuard then
    IO.println "PASS HOL-oracle Call arity mismatch (clock 5, x = ValWord 3w)"
  else IO.println "FAIL HOL-oracle Call arity mismatch (clock 5, x = ValWord 3w)"
  if oracleShapeGuard then
    IO.println "PASS HOL-oracle Call shape mismatch (clock 5, x = ValWord 3w)"
  else IO.println "FAIL HOL-oracle Call shape mismatch (clock 5, x = ValWord 3w)"
  if callFallThroughGuard then
    IO.println "PASS source Call callee fallthrough rejects with Error and callee locals"
  else IO.println "FAIL source Call callee fallthrough rejects with Error and callee locals"
  if callBreakGuard then
    IO.println "PASS source Call callee break rejects with Error, callee locals, and absent caller x"
  else IO.println "FAIL source Call callee break rejects with Error, callee locals, and absent caller x"
  if callContinueGuard then
    IO.println "PASS source Call callee continue rejects with Error and callee locals"
  else IO.println "FAIL source Call callee continue rejects with Error and callee locals"
  if callCalleeErrorGuard then
    IO.println "PASS source Call callee error propagates cleared locals"
  else IO.println "FAIL source Call callee error propagates cleared locals"
  if callReturnShapeAcceptGuard then
    IO.println "PASS source Call accepts the declared One return shape"
  else IO.println "FAIL source Call accepts the declared One return shape"
  if callBadReturnShapeGuard then
    IO.println "PASS code-map Call invalid return shape rejects with Error (clock 4)"
  else IO.println "FAIL code-map Call invalid return shape rejects with Error (clock 4)"
  if callBadReturnShapeParamGuard then
    IO.println "PASS code-map Call invalid return shape leaves no parameter local"
  else IO.println "FAIL code-map Call invalid return shape leaves no parameter local"
  if decCallBadReturnShapeGuard then
    IO.println "PASS code-map DecCall invalid return shape rejects with Error (clock 4)"
  else IO.println "FAIL code-map DecCall invalid return shape rejects with Error (clock 4)"
  if callGoodReturnShapeGuard then
    IO.println "PASS code-map Call valid return shape returns its value"
  else IO.println "FAIL code-map Call valid return shape returns its value"
  if callInvalidReturnShapeGuard then
    IO.println "PASS code-map Call Named-Other invalid return shape rejects with Error (clock 4)"
  else IO.println "FAIL code-map Call Named-Other invalid return shape rejects with Error (clock 4)"
  pure (callGuard && stateCodeGuard)

end Flapjack.Test.PanSemCallErrorExactParity

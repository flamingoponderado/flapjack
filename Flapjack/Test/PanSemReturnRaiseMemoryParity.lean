import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiCore

/-!
Direct regression for the source `PanSemState` code-map `Return`/`Raise`
equations.  The payload expressions read the source state's memory, so a
present word cell exercises the state-derived memory domain while an address
outside `memaddrs` exercises the `SOME Error` rejection.  The expected values
are the original-HOL `EVAL` rows in
`scripts/hol-probes/pan_sem_return_raise_memory_probe.out`:

* `ret_mem_fail_result=SOME Error`, `ret_mem_fail_locals=SOME (ValWord 3w)`,
  `ret_mem_fail_clock=5`;
* `ret_mem_ok_result=SOME (Return (ValWord 119w))`, `ret_mem_ok_locals=NONE`;
* `raise_mem_fail_result=SOME Error`, `raise_mem_fail_locals=SOME (ValWord 3w)`;
* `raise_mem_badshape_result=SOME Error`,
  `raise_mem_badshape_locals=SOME (ValWord 3w)`;
* `raise_mem_ok_result=SOME (Exception «E» (ValWord 119w))`,
  `raise_mem_ok_locals=NONE`.

This module is untagged infrastructure: the reduced `PanValueFfiClockResult`
encoding is not literally HOL's `(result option # state)` type, so no `@[hol]`
attribute is attached.
-/

namespace Flapjack.Test.PanSemReturnRaiseMemoryParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

/-- Source memory with a present word cell at address `8` and a zero fallback. -/
private def exactMemory : Word64 → Option (PanValue Word64) :=
  fun address =>
    if address == 8 then some (.word (BitVec.ofNat 64 0x77)) else some (.word 0)

private def exactDomain : Word64 → Bool :=
  fun address => address == 8

private def emptyDomain : Word64 → Bool := fun _ => false

/-- The source `eshapes` map: `E` is declared with shape `One`. -/
private def shapesOne : ExceptionId → Option Shape :=
  fun exception => if exception == "E" then some .one else none

/-- The source `eshapes` map: `E` is declared with a non-`One` shape. -/
private def shapesBad : ExceptionId → Option Shape :=
  fun exception => if exception == "E" then some (.named "Other") else none

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

private def localsWordSeven : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 7) else none

/-- State-owned source state used by the memory-reading guards. -/
private def sourceState (clock : Nat) (locals : VarName → Option (PanValue Word64))
    (memory : Word64 → Option (PanValue Word64)) (domain : Word64 → Bool)
    (shapes : ExceptionId → Option Shape) : PanSemState Word64 (FfiState Unit) :=
  { locals := locals
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := shapes
    memory := memory
    memaddrs := domain
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

/-- State with a present memory cell at address `8` and local `x`. -/
private def memoryState (clock : Nat) (shapes : ExceptionId → Option Shape) :
    PanSemState Word64 (FfiState Unit) :=
  sourceState clock localsWordX exactMemory exactDomain shapes

/-- State whose source evaluation fails immediately (no locals, no memory). -/
private def emptyState : PanSemState Word64 (FfiState Unit) :=
  sourceState 5 (fun _ => none) (fun _ => none) emptyDomain (fun _ => none)

/-- State whose source evaluation succeeds with `.word 7`. -/
private def wordState (shapes : ExceptionId → Option Shape) :
    PanSemState Word64 (FfiState Unit) :=
  sourceState 5 localsWordSeven (fun _ => none) emptyDomain shapes

private def evaluate (state : PanSemState Word64 (FfiState Unit)) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

private def isWordValue (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

private def isNoneOption : Option (PanValue Word64) → Bool
  | none => true
  | some _ => false

private def isErrorKeeping (clock localValue : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .error locals _ _ _ => n == clock && isWordValue localValue (locals "x")
      | _ => false
  | _ => false

private def isReturnedWith (clock expected : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .returned locals _ _ _ [value] =>
          n == clock && isNoneOption (locals "x") && isWordValue expected value
      | _ => false
  | _ => false

private def isRaisedWith (clock : Nat) (exceptionId : String) (expected : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control control, n) =>
      match control with
      | .raised locals _ _ _ exception value =>
          n == clock && isNoneOption (locals "x") && exception == exceptionId &&
            isWordValue expected value
      | _ => false
  | _ => false

private def loadHit : Exp Word64 := .load Shape.one (.const 8)

private def loadMiss : Exp Word64 := .load Shape.one (.const 11)

private def returnMissGuard : Bool :=
  isErrorKeeping 5 3 (evaluate (memoryState 5 (fun _ => none)) (.return loadMiss))

private def returnHitGuard : Bool :=
  isReturnedWith 5 119 (evaluate (memoryState 5 (fun _ => none)) (.return loadHit))

private def raiseMissGuard : Bool :=
  isErrorKeeping 5 3 (evaluate (memoryState 5 shapesOne) (.raise "E" loadMiss))

private def raiseBadShapeGuard : Bool :=
  isErrorKeeping 5 3 (evaluate (memoryState 5 shapesBad) (.raise "E" loadHit))

private def raiseHitGuard : Bool :=
  isRaisedWith 5 "E" 119 (evaluate (memoryState 5 shapesOne) (.raise "E" loadHit))

private def exactGuard : Bool :=
  returnMissGuard && returnHitGuard && raiseMissGuard && raiseBadShapeGuard &&
    raiseHitGuard

#guard exactGuard

/-- `Return` whose payload fails to evaluate returns `SOME Error` over the full
    source state. -/
theorem returnMiss_eq :
    evaluate emptyState (.return (.var .local "z")) =
      some (.control (.error emptyState.locals emptyState.globals
        emptyState.memory emptyState.ffi), emptyState.clock) := by
  simp (config := { decide := true }) [evaluate, emptyState, sourceState,
    panSemEvaluateRiscV64CodeState, panSemEvaluateWordCodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemProgFuel,
    panSemExpFuel, panSemCodeBodyFuel, panSemBitVec64BytesInWord,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf,
    evalPanValueFfiLeafControl, panValueReturnResult, evalPanValueExpWith,
    evalPanValueExp]

/-- `Raise` whose payload fails to evaluate returns `SOME Error` over the full
    source state. -/
theorem raiseMiss_eq :
    evaluate emptyState (.raise "E" (.var .local "z")) =
      some (.control (.error emptyState.locals emptyState.globals
        emptyState.memory emptyState.ffi), emptyState.clock) := by
  simp (config := { decide := true }) [evaluate, emptyState, sourceState,
    panSemEvaluateRiscV64CodeState, panSemEvaluateWordCodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemProgFuel,
    panSemExpFuel, panSemCodeBodyFuel, panSemBitVec64BytesInWord,
    evalPanValueFfiClockCodeProg, evalPanValueExpWith, evalPanValueExp]

/-- `Raise` whose payload shape does not match the declared shape returns
    `SOME Error` over the full source state. -/
theorem raiseBadShape_eq :
    evaluate (wordState shapesBad) (.raise "E" (.var .local "x")) =
      some (.control (.error (wordState shapesBad).locals
        (wordState shapesBad).globals
        (wordState shapesBad).memory
        (wordState shapesBad).ffi),
        (wordState shapesBad).clock) := by
  simp (config := { decide := true }) [evaluate, wordState, sourceState, shapesBad,
    panSemEvaluateRiscV64CodeState, panSemEvaluateWordCodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemProgFuel,
    panSemExpFuel, panSemCodeBodyFuel, panSemBitVec64BytesInWord,
    evalPanValueFfiClockCodeProg, evalPanValueExpWith, evalPanValueExp,
    panValueShape, panShapeMatches, localsWordSeven]

def runChecks : IO Bool := do
  if returnMissGuard then
    IO.println "PASS source Return eval failure keeps state and clock"
  else IO.println "FAIL source Return eval failure keeps state and clock"
  if returnHitGuard then
    IO.println "PASS source Return memory read returns the cell"
  else IO.println "FAIL source Return memory read returns the cell"
  if raiseMissGuard then
    IO.println "PASS source Raise eval failure keeps state and clock"
  else IO.println "FAIL source Raise eval failure keeps state and clock"
  if raiseBadShapeGuard then
    IO.println "PASS source Raise shape mismatch keeps state and clock"
  else IO.println "FAIL source Raise shape mismatch keeps state and clock"
  if raiseHitGuard then
    IO.println "PASS source Raise memory read raises the matched value"
  else IO.println "FAIL source Raise memory read raises the matched value"
  pure exactGuard

end Flapjack.Test.PanSemReturnRaiseMemoryParity

import Flapjack.Pancake.Semantics.PanSem
import Flapjack.Test.PanValueFfiCore

/-!
# PanSem `ExtCall` Error parity

HOL `panSem` (`cakeml/pancake/semantics/panSemScript.sml:716-729`) returns
`(SOME Error, s)` with the unchanged state when an `ExtCall` argument expression
fails to evaluate, when an argument is not a word, or when the byte read fails.
The byte-read failure is driven, in the original HOL probe, by an empty
`memaddrs` set while `memory` still returns `Word 0w`; the argument-evaluation
failure uses an unbound local.  These guards assert that the production source
evaluator `panSemEvaluateCodeStateWithPostState` returns an explicit Error
control result for all three branches, and that the returned state preserves
locals, globals, memory and observable FFI cells with an unchanged clock. The
same checks of the stepped evaluator `evalPanValueFfiProgSteps` moved to
stepped-flapjack with the stepped semantics (#1251).

Beyond the sampled `Bool` guards (which can only inspect decidable cells, as
`PanSemState` has no `DecidableEq`), three kernel-checked `clocked*_full`
reduction theorems establish the exact Error result. They equate the entire
post-state record, including all function fields, with the input state.

The HOL oracle is `scripts/hol-probes/pan_sem_extcall_error_probe.out`.
-/

namespace Flapjack.Test.PanSemExtCallErrorParity

open Flapjack Flapjack.RiscV

private abbrev Word64 := Word 64

def extState (clock : Nat) : PanSemState Word64 (FfiState Unit) :=
  { locals := fun name =>
      if name == "x" then some (.word (BitVec.ofNat 64 3))
      else if name == "s" then some (.rStruct [])
      else none
    globals := fun name => if name == "g" then some (.word (BitVec.ofNat 64 4)) else none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := fun _ => some (.word (BitVec.ofNat 64 0))
    memaddrs := fun _ => false
    sharedMemaddrs := fun _ => false
    clock := clock
    be := false
    ffi := statefulTestFfiState
    baseAddress := 0
    topAddress := 100 }

def emptyAccess : PanValueMemoryAccess Word64 :=
  panValueMemoryAccessOfModel RiscV.panRiscVMemoryModel (domain := fun _ => false)

/-- With an empty read domain every byte read fails, so reading `n + 1` bytes
    yields `none`. -/
theorem emptyRead_succ (context : PanValueFfiContext Word64)
    (memory : Word64 → Option (PanValue Word64)) (n : Nat) (address : Word64) :
    panValueFfiReadBytes emptyAccess context memory (BitVec.ofNat 64 8) address (n + 1) = none := by
  simp [panValueFfiReadBytes, emptyAccess, panValueMemoryAccessOfModel, panModelReadByte,
    panRiscVMemoryModel, panRiscVByteAlign]

theorem emptyRead_one (context : PanValueFfiContext Word64)
    (memory : Word64 → Option (PanValue Word64)) (address : Word64) :
    panValueFfiReadBytes emptyAccess context memory (BitVec.ofNat 64 8) address 1 = none :=
  emptyRead_succ context memory 0 address

def nonwordProgram : Prog Word64 :=
  .extCall "f" (.var .local "s") (.const 0) (.const 0) (.const 0)

def readFailProgram : Prog Word64 :=
  .extCall "f" (.const 0) (.const 1) (.const 0) (.const 0)

/-- An `ExtCall` whose first argument expression fails to evaluate (unbound
    local).  HOL returns `(SOME Error, s)`; the production evaluator must not
    collapse this to the fuel-exhaustion `none`. -/
def argFailProgram : Prog Word64 :=
  .extCall "f" (.var .local "missing") (.const 0) (.const 0) (.const 0)

def clockedEvaluate (clock : Nat) (program : Prog Word64)
    (memoryAccess : Option (PanValueMemoryAccess Word64) := none) :
    Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit)) :=
  panSemEvaluateCodeStateWithPostState statefulTestContext statefulTestPrimitive
    statefulTestHandler (BitVec.ofNat 64 8) (extState clock) program
    (memoryAccess := memoryAccess)

private def isWord (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

/-! ## Kernel-checked full post-state equality

    The `Bool` guards below sample representative cells only (PanSemState has no
    decidable equality).  The following theorems instead prove, by reduction of
    the whole evaluator, that each Error branch returns exactly the input state
    `extState 5` — i.e. every field and every function is preserved — and that
    the control result's locals/globals/memory/ffi are the input ones. -/

theorem clockedNonword_full : clockedEvaluate 5 nonwordProgram =
    some ((.control (.error (extState 5).locals (extState 5).globals
      (extState 5).memory statefulTestFfiState), 5), extState 5) := by
  simp (config := { decide := true }) [clockedEvaluate, panSemEvaluateCodeStateWithPostState,
    panSemEvaluateCodeState, panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel,
    panSemCodeStateAfter, evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl, panValueFfiExtCallResult, evalPanValueExpsWith,
    evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp, extState,
    nonwordProgram]

theorem clockedArgFail_full : clockedEvaluate 5 argFailProgram =
    some ((.control (.error (extState 5).locals (extState 5).globals
      (extState 5).memory statefulTestFfiState), 5), extState 5) := by
  simp (config := { decide := true }) [clockedEvaluate, panSemEvaluateCodeStateWithPostState,
    panSemEvaluateCodeState, panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel,
    panSemCodeStateAfter, evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl, panValueFfiExtCallResult, evalPanValueExpsWith,
    evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp, extState,
    argFailProgram]

theorem clockedReadFail_full : clockedEvaluate 5 readFailProgram (some emptyAccess) =
    some ((.control (.error (extState 5).locals (extState 5).globals
      (extState 5).memory statefulTestFfiState), 5), extState 5) := by
  simp (config := { decide := true }) [clockedEvaluate, panSemEvaluateCodeStateWithPostState,
    panSemEvaluateCodeState, panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel,
    panSemCodeStateAfter, evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl, panValueFfiExtCallResult, evalPanValueExpsWith,
    evalPanValueExps, evalPanValueExp.evalPanValueExps, evalPanValueExp, extState,
    readFailProgram, panValueFfiExtCall, emptyRead_one, statefulTestContext]

private def ffiObservable (ffi : FfiState Unit) : Bool :=
  ffi.state == () && decide (ffi.ioEvents = ([] : List FfiEvent))

private def clockedErrorPreserving (clock : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit × PanSemState Word64 (FfiState Unit))) :
    Bool :=
  match result with
  | some ((.control (.error locals globals memory ffi), n), post) =>
      n == clock
        && isWord 3 (locals "x") && isWord 4 (globals "g") && isWord 0 (memory 0)
        && ffiObservable ffi
        && post.clock == clock
        && isWord 3 (post.locals "x") && isWord 4 (post.globals "g")
        && isWord 0 (post.memory 0) && ffiObservable post.ffi
  | _ => false

def clockedNonwordGuard : Bool :=
  clockedErrorPreserving 5 (clockedEvaluate 5 nonwordProgram)

def clockedReadFailGuard : Bool :=
  clockedErrorPreserving 5 (clockedEvaluate 5 readFailProgram (some emptyAccess))

def clockedArgFailGuard : Bool :=
  clockedErrorPreserving 5 (clockedEvaluate 5 argFailProgram)

def extCallErrorGuard : Bool :=
  clockedNonwordGuard && clockedReadFailGuard && clockedArgFailGuard

#guard extCallErrorGuard

def runChecks : IO Bool := do
  IO.println (if clockedNonwordGuard then
    "PASS panSem ExtCall non-word argument rejected with unchanged state"
    else "FAIL panSem ExtCall non-word argument rejected with unchanged state")
  IO.println (if clockedReadFailGuard then
    "PASS panSem ExtCall failed byte read rejected with unchanged state"
    else "FAIL panSem ExtCall failed byte read rejected with unchanged state")
  IO.println (if clockedArgFailGuard then
    "PASS panSem ExtCall failed argument evaluation rejected with unchanged state"
    else "FAIL panSem ExtCall failed argument evaluation rejected with unchanged state")
  IO.println (if extCallErrorGuard then
    "PASS panSem ExtCall Error preserves the complete post state (kernel-checked)"
    else "FAIL panSem ExtCall Error preserves the complete post state (kernel-checked)")
  pure extCallErrorGuard

end Flapjack.Test.PanSemExtCallErrorParity

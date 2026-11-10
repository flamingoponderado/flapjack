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
# Exact-source PanSem `If` Error parity

The original HOL `panSemScript$evaluate_def` `If` case returns `SOME Error` with
the unchanged state when the condition expression fails to evaluate or does not
produce a word value.  This module checks the corresponding untagged
state-owned code-map equation against the direct HOL oracle
`scripts/hol-probes/pan_sem_ite_e2e_probe.out` (`if_nonword_result=SOME Error`,
`if_fail_result=SOME Error`). The checks of the non-clocked evaluator
moved to stepped-flapjack with the stepped semantics (#1251).
-/

namespace Flapjack.Test.PanSemIteErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain (address : Word64) : Bool := address == 8

private def exactMemory : Word64 → Option (PanValue Word64) := fun _ => some (.word 0)

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

/-- State-owned source state used by the `If` guards: local `x` holds a word. -/
private def sourceState : PanSemState Word64 (FfiState Unit) :=
  { locals := localsWordX
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := exactMemory
    memaddrs := exactDomain
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

private def evaluate (state : PanSemState Word64 (FfiState Unit)) (program : Prog Word64) :
    Option (PanValueFfiClockResult Word64 Unit) :=
  panSemEvaluateRiscV64CodeState statefulTestContext statefulTestPrimitive
    statefulTestHandler state program

private def isWordOption (expected : Nat) : Option (PanValue Word64) → Bool
  | some (.word value) => value == BitVec.ofNat 64 expected
  | _ => false

/-- Matches an `Error` control result at `clock` whose `x` local is unchanged. -/
private def isErrorKeepingX (clock value : Nat)
    (result : Option (PanValueFfiClockResult Word64 Unit)) : Bool :=
  match result with
  | some (.control (.error locals globals _ _), n) =>
      n == clock && isWordOption value (locals "x") && (globals "g").isNone
  | _ => false

/-- A non-word condition value (`RStruct []`). -/
private def nonwordConditionProgram : Prog Word64 :=
  .ite (.rStruct []) .skip .skip

/-- A condition whose evaluation fails (unbound local `z`). -/
private def failedConditionProgram : Prog Word64 :=
  .ite (.var .local "z") .skip .skip

private def iteNonwordGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate sourceState nonwordConditionProgram)

private def iteFailedGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate sourceState failedConditionProgram)

private def iteErrorGuard : Bool :=
  iteNonwordGuard && iteFailedGuard

#guard iteErrorGuard

/-- The kernel-checked code-map `If` non-word-condition equation at clock 5. -/
theorem iteNonword_eq :
    evaluate sourceState nonwordConditionProgram =
      some (.control (.error localsWordX (fun _ => none) exactMemory
        statefulTestFfiState), 5) := by
  simp (config := { decide := true }) [evaluate, sourceState, nonwordConditionProgram,
    panSemEvaluateRiscV64CodeState, panSemEvaluateWordCodeState,
    panSemEvaluateCodeStateWithMemoryModel, panSemEvaluateCodeState,
    panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemProgFuel,
    panSemExpFuel, panSemCodeBodyFuel, panSemBitVec64BytesInWord,
    evalPanValueFfiClockCodeProg, panValueIteConditionValue,
    evalPanValueExpWith, evalPanValueExp]

def runChecks : IO Bool := do
  if iteNonwordGuard then
    IO.println "PASS source If non-word condition keeps state and clock"
  else
    IO.println "FAIL source If non-word condition keeps state and clock"
  if iteFailedGuard then
    IO.println "PASS source If failing condition keeps state and clock"
  else
    IO.println "FAIL source If failing condition keeps state and clock"
  pure iteErrorGuard

end Flapjack.Test.PanSemIteErrorExactParity

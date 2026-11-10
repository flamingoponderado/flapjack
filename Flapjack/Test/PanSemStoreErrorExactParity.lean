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
# Exact-source PanSem `Store` Error parity

The original HOL `panSemScript$evaluate_def` `Store` case returns `SOME Error`
with the unchanged state when the address expression fails to evaluate, when
the stored-value expression fails to evaluate, or when the word store fails
(for example when the address is outside the store's domain).  This module
checks the corresponding untagged state-owned code-map equations against the
direct HOL oracle `scripts/hol-probes/pan_sem_store_error_probe.out`. The
checks of the non-clocked evaluator moved to stepped-flapjack with the stepped
semantics (#1251).
-/

namespace Flapjack.Test.PanSemStoreErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain (address : Word64) : Bool := address == 8

private def exactMemory : Word64 → Option (PanValue Word64) := fun _ => some (.word 0)

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

/-- State-owned source state used by the memory guards: local `x` holds a word
    and the store domain contains address `8` only when `domain` says so. -/
private def sourceState (domain : Word64 → Bool) :
    PanSemState Word64 (FfiState Unit) :=
  { locals := localsWordX
    globals := fun _ => none
    structs := []
    code := []
    exceptionShapes := fun _ => none
    memory := exactMemory
    memaddrs := domain
    sharedMemaddrs := fun _ => false
    clock := 5
    be := false
    ffi := statefulTestFfiState
    baseAddress := BitVec.ofNat 64 0
    topAddress := BitVec.ofNat 64 100 }

private def emptyDomain : Word64 → Bool := fun _ => false

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

private def storeAddressFailProgram : Prog Word64 :=
  .store (.var .local "z") (.const 7)

private def storeValueFailProgram : Prog Word64 :=
  .store (.const 0) (.var .local "z")

private def storeDomainFailProgram : Prog Word64 :=
  .store (.const 0) (.const 7)

private def storeKeywordState : PanSemState Word64 (FfiState Unit) :=
  sourceState exactDomain

private def storeAddressFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate storeKeywordState storeAddressFailProgram)

private def storeValueFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate storeKeywordState storeValueFailProgram)

private def storeDomainFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (sourceState emptyDomain) storeDomainFailProgram)

private def storeErrorGuard : Bool :=
  storeAddressFailGuard && storeValueFailGuard && storeDomainFailGuard

#guard storeErrorGuard

/-- The kernel-checked code-map `Store` failing-address equation at clock 5. -/
theorem storeAddressFail_eq :
    evaluate storeKeywordState storeAddressFailProgram =
      some (.control (.error localsWordX (fun _ => none) exactMemory
        statefulTestFfiState), 5) := by
  simp (config := { decide := true }) [evaluate, storeKeywordState, sourceState,
    storeAddressFailProgram, panSemEvaluateRiscV64CodeState,
    panSemEvaluateWordCodeState, panSemEvaluateCodeStateWithMemoryModel,
    panSemEvaluateCodeState, panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel, panSemProgFuel,
    panSemExpFuel, panSemCodeBodyFuel, panSemBitVec64BytesInWord,
    evalPanValueFfiClockCodeProg,
    evalPanValueFfiClockLeaf, evalPanValueFfiLeafControl, panValueStoreResult,
    evalPanValueExpWith, evalPanValueExp, localsWordX]

def runChecks : IO Bool := do
  if storeAddressFailGuard then
    IO.println "PASS source Store failing address keeps state and clock"
  else
    IO.println "FAIL source Store failing address keeps state and clock"
  if storeValueFailGuard then
    IO.println "PASS source Store failing value keeps state and clock"
  else
    IO.println "FAIL source Store failing value keeps state and clock"
  if storeDomainFailGuard then
    IO.println "PASS source Store domain failure keeps state and clock"
  else
    IO.println "FAIL source Store domain failure keeps state and clock"
  pure storeErrorGuard

end Flapjack.Test.PanSemStoreErrorExactParity

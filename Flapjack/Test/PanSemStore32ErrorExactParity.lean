import Flapjack.Pancake.Semantics.PanSemStateEval
import Flapjack.Test.PanValueFfiCore

/-!
# Exact-source PanSem `Store32`/`StoreByte` Error parity

The original HOL `panSemScript$evaluate_def` `Store32` and `StoreByte` cases
return `SOME Error` with the unchanged state when the address expression fails
to evaluate, when the stored-value expression fails to evaluate, or when the
sized store fails (for example when the aligned address is outside the store's
domain).  This module checks the corresponding untagged state-owned code-map
equations against the direct HOL oracle
`scripts/hol-probes/pan_sem_store_error_probe.out`. The checks of the
non-clocked evaluator moved to stepped-flapjack with the stepped semantics
(#1251).
-/

namespace Flapjack.Test.PanSemStore32ErrorExactParity

open Flapjack
open Flapjack.RiscV

private abbrev Word64 := Word 64

private def exactDomain (address : Word64) : Bool := address == 8

private def emptyDomain : Word64 → Bool := fun _ => false

private def exactMemory : Word64 → Option (PanValue Word64) := fun _ => some (.word 0)

private def localsWordX : VarName → Option (PanValue Word64) :=
  fun name => if name == "x" then some (.word 3) else none

/-- State-owned source state used by the sized-store guards: local `x` holds a
    word and the store domain contains address `8` only when `domain` says so. -/
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

private def store32AddressFailProgram : Prog Word64 :=
  .store32 (.var .local "z") (.const 7)

private def store32ValueFailProgram : Prog Word64 :=
  .store32 (.const 0) (.var .local "z")

private def store32DomainFailProgram : Prog Word64 :=
  .store32 (.const 0) (.const 7)

private def storeByteAddressFailProgram : Prog Word64 :=
  .storeByte (.var .local "z") (.const 7)

private def storeByteValueFailProgram : Prog Word64 :=
  .storeByte (.const 0) (.var .local "z")

private def storeByteDomainFailProgram : Prog Word64 :=
  .storeByte (.const 0) (.const 7)

private def store32AddressFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (sourceState exactDomain) store32AddressFailProgram)

private def store32ValueFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (sourceState exactDomain) store32ValueFailProgram)

private def store32DomainFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (sourceState emptyDomain) store32DomainFailProgram)

private def storeByteAddressFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (sourceState exactDomain) storeByteAddressFailProgram)

private def storeByteValueFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (sourceState exactDomain) storeByteValueFailProgram)

private def storeByteDomainFailGuard : Bool :=
  isErrorKeepingX 5 3 (evaluate (sourceState emptyDomain) storeByteDomainFailProgram)

private def store32ErrorGuard : Bool :=
  store32AddressFailGuard && store32ValueFailGuard && store32DomainFailGuard &&
    storeByteAddressFailGuard && storeByteValueFailGuard && storeByteDomainFailGuard

#guard store32ErrorGuard

/-- The kernel-checked code-map `Store32` failing-address equation at clock 5. -/
theorem store32AddressFail_eq :
    evaluate (sourceState exactDomain) store32AddressFailProgram =
      some (.control (.error localsWordX (fun _ => none) exactMemory
        statefulTestFfiState), 5) := by
  simp (config := { decide := true }) [evaluate, sourceState,
    store32AddressFailProgram, panSemEvaluateRiscV64CodeState,
    panSemEvaluateWordCodeState, panSemEvaluateCodeStateWithMemoryModel,
    panSemEvaluateCodeState, panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel,
    panSemProgFuel, panSemExpFuel, panSemCodeBodyFuel, panSemBitVec64BytesInWord,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf,
    evalPanValueFfiLeafControl, panValueStore32Result, evalPanValueExpWith,
    evalPanValueExp, localsWordX]

/-- The kernel-checked code-map `StoreByte` failing-address equation at clock 5. -/
theorem storeByteAddressFail_eq :
    evaluate (sourceState exactDomain) storeByteAddressFailProgram =
      some (.control (.error localsWordX (fun _ => none) exactMemory
        statefulTestFfiState), 5) := by
  simp (config := { decide := true }) [evaluate, sourceState,
    storeByteAddressFailProgram, panSemEvaluateRiscV64CodeState,
    panSemEvaluateWordCodeState, panSemEvaluateCodeStateWithMemoryModel,
    panSemEvaluateCodeState, panSemEvaluateCodeStateWithFuel, panSemCodeEvaluateFuel,
    panSemProgFuel, panSemExpFuel, panSemCodeBodyFuel, panSemBitVec64BytesInWord,
    evalPanValueFfiClockCodeProg, evalPanValueFfiClockLeaf,
    evalPanValueFfiLeafControl, panValueStoreByteResult, evalPanValueExpWith,
    evalPanValueExp, localsWordX]

def runChecks : IO Bool := do
  if store32AddressFailGuard then
    IO.println "PASS source Store32 failing address keeps state and clock"
  else
    IO.println "FAIL source Store32 failing address keeps state and clock"
  if store32ValueFailGuard then
    IO.println "PASS source Store32 failing value keeps state and clock"
  else
    IO.println "FAIL source Store32 failing value keeps state and clock"
  if store32DomainFailGuard then
    IO.println "PASS source Store32 domain failure keeps state and clock"
  else
    IO.println "FAIL source Store32 domain failure keeps state and clock"
  if storeByteAddressFailGuard then
    IO.println "PASS source StoreByte failing address keeps state and clock"
  else
    IO.println "FAIL source StoreByte failing address keeps state and clock"
  if storeByteValueFailGuard then
    IO.println "PASS source StoreByte failing value keeps state and clock"
  else
    IO.println "FAIL source StoreByte failing value keeps state and clock"
  if storeByteDomainFailGuard then
    IO.println "PASS source StoreByte domain failure keeps state and clock"
  else
    IO.println "FAIL source StoreByte domain failure keeps state and clock"
  pure store32ErrorGuard

end Flapjack.Test.PanSemStore32ErrorExactParity

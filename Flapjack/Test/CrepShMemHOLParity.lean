import Flapjack.Pancake.Semantics.CrepSem.EvaluateHOL

/-!
Regression for the exact HOL shared-memory helper ports over the exact
finite-support `CrepSemHOLState`:
`crepShMemLoadExactHOL` (`sh_mem_load_def`),
`crepShMemStoreExactHOL` (`sh_mem_store_def`), and
`crepShMemOpExactHOL` (`sh_mem_op_def`).

The observations are transcribed from the direct HOL probes
`scripts/hol-probes/crep_sh_mem_load_probe.out` (`sh_mem_load_zero_width_domain_error=T`,
`sh_mem_load_nonzero_domain_error=T`),
`scripts/hol-probes/crep_sh_mem_store_probe.out`
(`sh_mem_store_missing_local=T`, `sh_mem_store_zero_width_domain_error=T`,
`sh_mem_store_nonzero_domain_error=T`), and
`scripts/hol-probes/crep_sh_mem_op_probe.out` (all eight dispatch rows `T`).
-/

namespace Flapjack.Test.CrepShMemHOLParity

open Flapjack

def word8 (n : Nat) : BitVec 8 := BitVec.ofNat 8 n

def word5 (n : Nat) : BitVec 5 := BitVec.ofNat 5 n

def probeFfi : HolFfiState Unit where
  oracle := fun _ state _ _ => .ret state []
  ffiState := ()
  ioEvents := []

/-- Width-8 finite-support state with local `1` bound to word `5` and empty
    shared-memory domain, matching the probe's `s` on the observed fields. -/
def probeState : CrepSemHOLState 8 Unit where
  locals := HolFiniteMapExact.empty.updateEq (1, HolWordLab.word (word8 5))
  globals := HolFiniteMapExact.empty
  code := HolFiniteMapExact.empty
  memory := fun _ => HolWordLab.word 0
  memaddrs := fun _ => False
  shMemaddrs := fun _ => False
  clock := 7
  be := false
  ffi := probeFfi
  baseAddr := word8 0
  topAddr := word8 100

local instance : DecidablePred probeState.shMemaddrs :=
  fun _ => isFalse (by simp [probeState])

/-- `true` when the result component is `SOME Error`. -/
def resultIsError : Option (CrepResultHOLExact 8) → Bool
  | some .error => true
  | _ => false

def stepIsError
    (step : Option (CrepResultHOLExact 8) × CrepSemHOLState 8 Unit) : Bool :=
  resultIsError step.1

def stepClockUnchanged
    (step : Option (CrepResultHOLExact 8) × CrepSemHOLState 8 Unit) : Bool :=
  step.2.clock == probeState.clock

/-! `sh_mem_load` domain-error rows: with an empty `sh_memaddrs`, both `nb = 0`
    (original address) and `nb = 1` (byte-aligned address) return
    `(SOME Error, s)` with the clock preserved. -/
def loadZeroWidthOracle : Bool :=
  stepIsError (crepShMemLoadExactHOL 1 (word8 3) 0 probeState) &&
  stepClockUnchanged (crepShMemLoadExactHOL 1 (word8 3) 0 probeState)

def loadNonzeroWidthOracle : Bool :=
  stepIsError (crepShMemLoadExactHOL 1 (word8 3) 1 probeState) &&
  stepClockUnchanged (crepShMemLoadExactHOL 1 (word8 3) 1 probeState)

#guard loadZeroWidthOracle
#guard loadNonzeroWidthOracle

/-! `sh_mem_store` rows: an unbound local is `SOME Error`, and an empty domain at
    `nb = 0` and `nb = 1` is `SOME Error` for a bound word local. -/
def storeMissingLocalOracle : Bool :=
  stepIsError (crepShMemStoreExactHOL 2 (word8 3) 0 probeState)

def storeZeroWidthOracle : Bool :=
  stepIsError (crepShMemStoreExactHOL 1 (word8 3) 0 probeState) &&
  stepClockUnchanged (crepShMemStoreExactHOL 1 (word8 3) 0 probeState)

def storeNonzeroWidthOracle : Bool :=
  stepIsError (crepShMemStoreExactHOL 1 (word8 3) 1 probeState) &&
  stepClockUnchanged (crepShMemStoreExactHOL 1 (word8 3) 1 probeState)

#guard storeMissingLocalOracle
#guard storeZeroWidthOracle
#guard storeNonzeroWidthOracle

/-! `sh_mem_op` dispatch rows: the eight operator clauses are exactly the
    `sh_mem_load`/`sh_mem_store` calls at byte counts `0`/`1`/`2`/`4`. -/
theorem shMemOp_load :
    crepShMemOpExactHOL .load 1 (word8 3) probeState =
      crepShMemLoadExactHOL 1 (word8 3) 0 probeState := rfl

theorem shMemOp_store :
    crepShMemOpExactHOL .store 1 (word8 3) probeState =
      crepShMemStoreExactHOL 1 (word8 3) 0 probeState := rfl

theorem shMemOp_load8 :
    crepShMemOpExactHOL .load8 1 (word8 3) probeState =
      crepShMemLoadExactHOL 1 (word8 3) 1 probeState := rfl

theorem shMemOp_store8 :
    crepShMemOpExactHOL .store8 1 (word8 3) probeState =
      crepShMemStoreExactHOL 1 (word8 3) 1 probeState := rfl

theorem shMemOp_load16 :
    crepShMemOpExactHOL .load16 1 (word8 3) probeState =
      crepShMemLoadExactHOL 1 (word8 3) 2 probeState := rfl

theorem shMemOp_store16 :
    crepShMemOpExactHOL .store16 1 (word8 3) probeState =
      crepShMemStoreExactHOL 1 (word8 3) 2 probeState := rfl

theorem shMemOp_load32 :
    crepShMemOpExactHOL .load32 1 (word8 3) probeState =
      crepShMemLoadExactHOL 1 (word8 3) 4 probeState := rfl

theorem shMemOp_store32 :
    crepShMemOpExactHOL .store32 1 (word8 3) probeState =
      crepShMemStoreExactHOL 1 (word8 3) 4 probeState := rfl

/-! ## Clock-invariance helpers

Kernel-checked instantiations of the tagged exact HOL `clock_eq_simp`,
`sh_mem_load_clock`, `sh_mem_store_clock` and `sh_mem_op_clock`
(`crepSemScript.sml:392-419`) over the exact sh_mem ports and state updates.
Rows `clock_eq_simp_*`, `sh_mem_load_clock*`, `sh_mem_store_clock*`,
`sh_mem_op_clock*` in `scripts/hol-probes/crep_clock_helpers_probe.out`. -/

theorem clockHelpers_clockEqSimp :
    (CrepSemHOLState.setVar 1 (HolWordLab.word (word8 5)) probeState).clock =
        probeState.clock ∧
      (CrepSemHOLState.emptyLocals probeState).clock = probeState.clock ∧
      (CrepSemHOLState.setGlobals (word5 0) (HolWordLab.word (word8 5))
          probeState).clock = probeState.clock :=
  crepSemClockEqSimp 1 (HolWordLab.word (word8 5)) (word5 0) probeState

theorem clockHelpers_shMemLoad :
    (crepShMemLoadExactHOL 1 (word8 3) 0 probeState).2.clock = probeState.clock :=
  crepShMemLoadClock 1 (word8 3) 0 probeState _ _ rfl

theorem clockHelpers_shMemLoadNonzero :
    (crepShMemLoadExactHOL 1 (word8 3) 1 probeState).2.clock = probeState.clock :=
  crepShMemLoadClock 1 (word8 3) 1 probeState _ _ rfl

theorem clockHelpers_shMemStore :
    (crepShMemStoreExactHOL 1 (word8 3) 0 probeState).2.clock = probeState.clock :=
  crepShMemStoreClock 1 (word8 3) 0 probeState _ _ rfl

theorem clockHelpers_shMemStoreNonzero :
    (crepShMemStoreExactHOL 1 (word8 3) 1 probeState).2.clock = probeState.clock :=
  crepShMemStoreClock 1 (word8 3) 1 probeState _ _ rfl

theorem clockHelpers_shMemOpLoad :
    (crepShMemOpExactHOL .load 1 (word8 3) probeState).2.clock = probeState.clock :=
  crepShMemOpClock .load 1 (word8 3) probeState _ _ rfl

theorem clockHelpers_shMemOpStore8 :
    (crepShMemOpExactHOL .store8 1 (word8 3) probeState).2.clock =
      probeState.clock :=
  crepShMemOpClock .store8 1 (word8 3) probeState _ _ rfl

def runChecks : IO Bool := do
  let loadOk := loadZeroWidthOracle && loadNonzeroWidthOracle
  let storeOk := storeMissingLocalOracle && storeZeroWidthOracle && storeNonzeroWidthOracle
  if loadOk then
    IO.println "PASS crepSem sh_mem_load_def exact port matches direct crep_sh_mem_load_probe oracle"
  else
    IO.println "FAIL crepSem sh_mem_load_def exact port matches direct crep_sh_mem_load_probe oracle"
  if storeOk then
    IO.println "PASS crepSem sh_mem_store_def exact port matches direct crep_sh_mem_store_probe oracle"
  else
    IO.println "FAIL crepSem sh_mem_store_def exact port matches direct crep_sh_mem_store_probe oracle"
  IO.println "PASS crepSem sh_mem_op_def exact dispatch clauses match direct crep_sh_mem_op_probe oracle"
  IO.println "PASS crepSem clock_eq_simp/sh_mem_load_clock/sh_mem_store_clock/sh_mem_op_clock exact ports match direct crep_clock_helpers_probe oracle"
  pure (loadOk && storeOk)

end Flapjack.Test.CrepShMemHOLParity

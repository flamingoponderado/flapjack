import Flapjack.Compiler.Backend.Semantics.TargetSem.Evaluate

namespace Flapjack.Test.TargetSemEvaluateParity
open Flapjack Flapjack.Compiler.Encoders.Asm

-- The original probe updates an arbitrary 8-bit target/configuration with
-- exactly these fields. Unread fields remain universally quantified.
def fixture (mc : MachineConfig 8 Nat Nat) : MachineConfig 8 Nat Nat :=
  { mc with
    progAddresses := (fun _ => False), ffiEntryPcs := [], haltPc := 1,
    ccachePc := 2, target := { mc.target with
      getPc := (fun _ => 0),
      getReg := fun _ _ => 0 } }

-- Original HOL te_zero=T.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL mc ffi 0 7 = (.timeOut, 7, ffi) := rfl

-- Original HOL te_unknown=T.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL (fixture mc) ffi 1 7 = (.error, 7, ffi) := by
  simp [evaluateTargetHOL, fixture, Misc.findIndex]

-- Original HOL te_halt_success=T.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL { (fixture mc) with haltPc := 0 } ffi 1 7 =
      (.halt .success, 7, ffi) := by
  simp [evaluateTargetHOL, fixture]

-- Original HOL te_halt_resource=T.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL { (fixture mc) with
      haltPc := 0,
      target := { (fixture mc).target with getReg := fun _ _ => 9 } } ffi 1 7 =
      (.halt .resourceLimitHit, 7, ffi) := by
  simp [evaluateTargetHOL, fixture]

-- Original HOL te_cache=T: only the cache oracle is called, at index zero.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL { (fixture mc) with
      ccachePc := 0,
      ccacheInterfer := fun n (_, _, ms) => ms + n + 10 } ffi 1 7 =
      (.timeOut, 17, ffi) := by
  simp [evaluateTargetHOL, fixture, applyOracleHOL]

-- Original HOL te_shared_missing=T.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL { (fixture mc) with
      ffiEntryPcs := [0],
      ffiNames := [.sharedMem .mappedRead], mmioInfo := [] } ffi 1 7 =
      (.error, 7, ffi) := by
  simp [evaluateTargetHOL, fixture, Misc.findIndex, holEl, holHd, sptAListLookup]

-- Original HOL te_external_mmio=T: a configured MMIO entry rejects ExtCall.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL { (fixture mc) with
      ffiEntryPcs := [0],
      ffiNames := [.extCall (Basis.Pure.MlString.MlString.implode [120])],
      mmioInfo := [(0, 1, .addr 0 0, 0, 0)] } ffi 1 7 = (.error, 7, ffi) := by
  simp [evaluateTargetHOL, fixture, Misc.findIndex, holEl, holHd, sptAListLookup]


-- Original HOL te_cache_shift=T: the second oracle index is one.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL { (fixture mc) with
      ccachePc := 0, ccacheInterfer := fun n (_, _, ms) => ms + n + 10 } ffi 2 7 =
      (.timeOut, 28, ffi) := by
  simp [evaluateTargetHOL, fixture, applyOracleHOL, holShiftSeq]

-- Original HOL te_normal_priority_encoding_fail=T: normal stepping wins
-- over halt, and an empty encoding cannot meet the strict drop bound.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL { (fixture mc) with
      progAddresses := fun _ => True, haltPc := 0,
      target := { (fixture mc).target with
        config := { mc.target.config with encode := fun _ => [] } } } ffi 1 7 =
      (.error, 7, ffi) := by
  simp [evaluateTargetHOL, fixture, encodedBytesInMemHOL]


def emptyExternal (mc : MachineConfig 8 Nat Nat) : MachineConfig 8 Nat Nat :=
  { (fixture mc) with
    ffiEntryPcs := [0], ffiNames := [.extCall (Basis.Pure.MlString.MlString.implode [])],
    mmioInfo := [], ffiInterfer := fun n (_, _, ms) => ms + n + 10 }

-- Original HOL te_empty_external=T. Empty-name calls return the original FFI.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL (emptyExternal mc) ffi 1 7 = (.timeOut, 17, ffi) := by
  simp [evaluateTargetHOL, emptyExternal, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, readFfiBytearraysHOL, readFfiBytearrayHOL, readBytearrayWordHOL,
    callFFIHOL, applyOracleHOL]

-- Original HOL te_empty_external_shift=T.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL (emptyExternal mc) ffi 2 7 = (.timeOut, 28, ffi) := by
  simp [evaluateTargetHOL, emptyExternal, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, readFfiBytearraysHOL, readFfiBytearrayHOL, readBytearrayWordHOL,
    callFFIHOL, applyOracleHOL, holShiftSeq]


def normal (mc : MachineConfig 8 Nat Nat) : MachineConfig 8 Nat Nat :=
  { (fixture mc) with
    progAddresses := fun _ => True, haltPc := 0,
    nextInterfer := fun n ms => ms + n + 10,
    target := { (fixture mc).target with
      config := { mc.target.config with encode := fun _ => [0], codeAlignment := 0 },
      getByte := fun _ _ => 0, next := fun ms => ms + 1, stateOk := fun _ => true } }

theorem normalEncoded (mc : MachineConfig 8 Nat Nat) (ms : Nat) :
    encodedBytesInMemHOL (normal mc).target.config ((normal mc).target.getPc ms)
      ((normal mc).target.getByte ms) (normal mc).progAddresses := by
  refine ⟨.inst .skip, 0, ?_⟩
  simp [normal, fixture, bytesInMemoryHOL]

-- Original HOL te_normal_success=T, including oracle-state result 18.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL (normal mc) ffi 1 7 = (.timeOut, 18, ffi) := by
  simp [evaluateTargetHOL, normal, fixture, applyOracleHOL]
  have he := normalEncoded mc 7
  simp [normal, fixture] at he
  simp only [he, if_true]

-- Original HOL te_normal_guard_rollback=T, rejecting state 18 after interference.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL { (normal mc) with
      target := { (normal mc).target with stateOk := fun ms => ms != 18 } } ffi 1 7 =
      (.error, 7, ffi) := by
  simp [evaluateTargetHOL, normal, fixture, applyOracleHOL]
  have he := normalEncoded mc 7
  simp [normal, fixture] at he
  simp only [he, if_true]


-- Original HOL te_normal_shift=T: next/oracle states are 8/18, then 19/30.
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    evaluateTargetHOL (normal mc) ffi 2 7 = (.timeOut, 30, ffi) := by
  simp [evaluateTargetHOL, normal, fixture, applyOracleHOL, holShiftSeq]
  have he := normalEncoded mc 7
  simp [normal, fixture] at he
  simp only [he, if_true]


def mmio (mc : MachineConfig 8 Nat Nat) (op : HolShmemOp) (nb : BitVec 8) :
    MachineConfig 8 Nat Nat :=
  { (fixture mc) with
    ffiEntryPcs := [0], ffiNames := [.sharedMem op],
    mmioInfo := [(0, nb, .addr 0 0, 0, 0)], sharedAddresses := fun _ => True,
    ffiInterfer := fun n (_, _, ms) => ms + n + 10,
    target := { (fixture mc).target with
      config := { mc.target.config with encode := fun _ => [] } } }

def returning : HolFfiState Nat :=
  { oracle := fun _ st _ bytes => .ret (st + 1) bytes, ffiState := 9, ioEvents := [] }
def terminal : HolFfiState Nat :=
  { oracle := fun _ _ _ _ => .final .failed, ffiState := 9, ioEvents := [] }

-- Original HOL te_mm_read_return=T. Whole returned FFI host/event state.
example (mc : MachineConfig 8 Nat Nat) :
    evaluateTargetHOL (mmio mc .mappedRead 0) returning 1 7 =
      (.timeOut, 17, { returning with
        ffiState := 10,
        ioEvents := [{
          name := .sharedMem .mappedRead, configuration := [0],
          bytes := [(0, 0)] }] }) := by
  simp [evaluateTargetHOL, mmio, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, isValidMappedRead, bytesInMemoryHOL, callFFIHOL, returning,
    applyOracleHOL, HolByte.wordToBytes, HolByte.wordToBytesAux, HolByte.getByte,
    HolByte.byteIndex]

-- Original HOL te_mm_write_return=T.
example (mc : MachineConfig 8 Nat Nat) :
    evaluateTargetHOL (mmio mc .mappedWrite 0) returning 1 7 =
      (.timeOut, 17, { returning with
        ffiState := 10,
        ioEvents := [{
          name := .sharedMem .mappedWrite, configuration := [0],
          bytes := [(0, 0), (0, 0)] }] }) := by
  simp [evaluateTargetHOL, mmio, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, isValidMappedWrite, bytesInMemoryHOL, callFFIHOL, returning,
    applyOracleHOL, HolByte.wordToBytes, HolByte.wordToBytesAux, HolByte.getByte,
    HolByte.byteIndex]

-- Original HOL te_mm_write_narrow=T.
example (mc : MachineConfig 8 Nat Nat) :
    evaluateTargetHOL (mmio mc .mappedWrite 1) returning 1 7 =
      (.timeOut, 17, { returning with
        ffiState := 10,
        ioEvents := [{
          name := .sharedMem .mappedWrite, configuration := [1],
          bytes := [(0, 0), (0, 0)] }] }) := by
  simp [evaluateTargetHOL, mmio, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, isValidMappedWrite, bytesInMemoryHOL, callFFIHOL, returning,
    applyOracleHOL, HolByte.wordToBytes, HolByte.wordToBytesAux, HolByte.getByte,
    HolByte.byteIndex]

-- Original HOL te_mm_read_final=T: original machine/FFI remain in the result.
example (mc : MachineConfig 8 Nat Nat) :
    evaluateTargetHOL (mmio mc .mappedRead 0) terminal 1 7 =
      (.halt (.ffiOutcome {
          name := .sharedMem .mappedRead, configuration := [0],
          bytes := [0], outcome := .failed }), 7, terminal) := by
  simp [evaluateTargetHOL, mmio, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, isValidMappedRead, bytesInMemoryHOL, callFFIHOL, terminal,
    HolByte.wordToBytes, HolByte.wordToBytesAux, HolByte.getByte, HolByte.byteIndex]

-- Original HOL te_mm_unshared=T.
example (mc : MachineConfig 8 Nat Nat) :
    evaluateTargetHOL { (mmio mc .mappedRead 0) with
      sharedAddresses := fun _ => False } returning 1 7 = (.error, 7, returning) := by
  simp [evaluateTargetHOL, mmio, fixture, Misc.findIndex, holEl, holHd, sptAListLookup]

-- Original HOL te_mm_invalid_size=T, even with an empty encoded template.
example (mc : MachineConfig 8 Nat Nat) :
    evaluateTargetHOL (mmio mc .mappedRead 3) returning 1 7 = (.error, 7, returning) := by
  simp [evaluateTargetHOL, mmio, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, isValidMappedRead]

end Flapjack.Test.TargetSemEvaluateParity

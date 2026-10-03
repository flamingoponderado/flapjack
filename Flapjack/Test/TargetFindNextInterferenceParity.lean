import Flapjack.Compiler.Backend.Semantics.TargetProps.FindNextInterference
import Flapjack.Test.TargetSemEvaluateParity

namespace Flapjack.Test.TargetFindNextInterferenceParity
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Test.TargetSemEvaluateParity

example {width : Nat} [NeZero width] {S P σ : Type}
    (mc : MachineConfig width S P) (ffi : HolFfiState σ) (ms : S) :
    findNextInterference mc ffi 0 ms = none := rfl

example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    findNextInterference (fixture mc) ffi 1 7 = none := by
  simp [findNextInterference, fixture, Misc.findIndex]
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    findNextInterference { (fixture mc) with haltPc := 0 } ffi 1 7 = none := by
  simp [findNextInterference, fixture]

def cache (mc : MachineConfig 8 Nat Nat) : MachineConfig 8 Nat Nat :=
  { (fixture mc) with
    ccachePc := 0, ccacheInterfer := fun n (_, _, ms) => ms + n + 10 }
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    findNextInterference (cache mc) ffi 1 7 =
      some (.ccApp 0 0 7 17,
        { (cache mc) with ccacheInterfer := holShiftSeq 1 (cache mc).ccacheInterfer }, ffi) := by
  simp [findNextInterference, cache, fixture, applyOracleHOL]

example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    findNextInterference { (fixture mc) with
      ffiEntryPcs := [0], ffiNames := [.sharedMem .mappedRead], mmioInfo := [] } ffi 1 7 = none := by
  simp [findNextInterference, fixture, Misc.findIndex, holEl, holHd, sptAListLookup]
example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    findNextInterference (emptyExternal mc) ffi 1 7 =
      some (.ffiApp 0 [] 7 17,
        { (emptyExternal mc) with ffiInterfer := holShiftSeq 1 (emptyExternal mc).ffiInterfer }, ffi) := by
  simp [findNextInterference, emptyExternal, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, readFfiBytearraysHOL, readFfiBytearrayHOL, readBytearrayWordHOL,
    callFFIHOL, applyOracleHOL]

example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    findNextInterference (normal mc) ffi 1 7 = none := by
  simp [findNextInterference, normal, fixture, applyOracleHOL]
  have he := normalEncoded mc 7
  simp [normal, fixture] at he
  simp only [he, if_true]
example (mc : MachineConfig 8 Nat Nat) :
    findNextInterference (mmio mc .mappedRead 0) terminal 1 7 = none := by
  simp [findNextInterference, mmio, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, isValidMappedRead, bytesInMemoryHOL, callFFIHOL, terminal,
    HolByte.wordToBytes, HolByte.wordToBytesAux, HolByte.getByte, HolByte.byteIndex]

example (mc : MachineConfig 8 Nat Nat) :
    findNextInterference (mmio mc .mappedRead 0) returning 1 7 =
      some (.ffiApp 0 [0] 7 17,
        { (mmio mc .mappedRead 0) with ffiInterfer := holShiftSeq 1 (mmio mc .mappedRead 0).ffiInterfer },
        { returning with ffiState := 10, ioEvents := [{
          name := .sharedMem .mappedRead, configuration := [0], bytes := [(0, 0)] }] }) := by
  simp [findNextInterference, mmio, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, isValidMappedRead, bytesInMemoryHOL,
    callFFIHOL, returning, applyOracleHOL, HolByte.wordToBytes,
    HolByte.wordToBytesAux, HolByte.getByte, HolByte.byteIndex]

example (mc : MachineConfig 8 Nat Nat) :
    findNextInterference (mmio mc .mappedWrite 0) returning 1 7 =
      some (.ffiApp 0 [0, 0] 7 17,
        { (mmio mc .mappedWrite 0) with ffiInterfer := holShiftSeq 1 (mmio mc .mappedWrite 0).ffiInterfer },
        { returning with ffiState := 10, ioEvents := [{
          name := .sharedMem .mappedWrite, configuration := [0], bytes := [(0, 0), (0, 0)] }] }) := by
  simp [findNextInterference, mmio, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, isValidMappedWrite, bytesInMemoryHOL,
    callFFIHOL, returning, applyOracleHOL, HolByte.wordToBytes,
    HolByte.wordToBytesAux, HolByte.getByte, HolByte.byteIndex]

example (mc : MachineConfig 8 Nat Nat) :
    findNextInterference (mmio mc .mappedWrite 1) returning 1 7 =
      some (.ffiApp 0 [0, 0] 7 17,
        { (mmio mc .mappedWrite 1) with ffiInterfer := holShiftSeq 1 (mmio mc .mappedWrite 1).ffiInterfer },
        { returning with ffiState := 10, ioEvents := [{
          name := .sharedMem .mappedWrite, configuration := [1], bytes := [(0, 0), (0, 0)] }] }) := by
  simp [findNextInterference, mmio, fixture, Misc.findIndex, holEl, holHd,
    sptAListLookup, isValidMappedWrite, bytesInMemoryHOL,
    callFFIHOL, returning, applyOracleHOL, HolByte.wordToBytes,
    HolByte.wordToBytesAux, HolByte.getByte, HolByte.byteIndex]

def normalCache (mc : MachineConfig 8 Nat Nat) : MachineConfig 8 Nat Nat :=
  { (fixture mc) with
    progAddresses := fun a => a = 0,
    nextInterfer := fun n ms => ms + n + 10,
    ccachePc := 2, ccacheInterfer := fun n (_, _, ms) => ms + n + 10,
    target := { (fixture mc).target with
      config := { mc.target.config with encode := fun _ => [0], codeAlignment := 0 },
      getByte := fun _ _ => 0, next := fun ms => ms + 1,
      stateOk := fun _ => true, getPc := fun ms => if ms < 10 then 0 else 2 } }

theorem normalCacheEncoded (mc : MachineConfig 8 Nat Nat) :
    encodedBytesInMemHOL (normalCache mc).target.config 0
      ((normalCache mc).target.getByte 7) (normalCache mc).progAddresses := by
  refine ⟨.inst .skip, 0, ?_⟩
  simp [normalCache, fixture, bytesInMemoryHOL]

example (mc : MachineConfig 8 Nat Nat) (ffi : HolFfiState Nat) :
    findNextInterference (normalCache mc) ffi 2 7 =
      some (.ccApp 0 0 18 28,
        { (normalCache mc) with
          nextInterfer := holShiftSeq 1 (normalCache mc).nextInterfer,
          ccacheInterfer := holShiftSeq 1 (normalCache mc).ccacheInterfer }, ffi) := by
  simp [findNextInterference, normalCache, fixture, applyOracleHOL]
  have he := normalCacheEncoded mc
  simp [normalCache, fixture] at he
  simp only [he, if_true]

end Flapjack.Test.TargetFindNextInterferenceParity

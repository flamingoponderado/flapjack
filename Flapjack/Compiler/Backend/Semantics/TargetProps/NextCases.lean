import Flapjack.Compiler.Backend.Semantics.TargetProps.NextInterference

namespace Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack Classical

/-- Literal source646: the full guarded external-call result and shifted interference oracle. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem nextInterferenceExtCall {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S) (index : Nat) (name : Flapjack.Basis.Pure.MlString.MlString)
    (bytes bytes2 newBytes : List (BitVec 8)) (newFfi : HolFfiState σ)
    (h : ¬ (mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs) ∧
      mc.target.getPc ms ≠ mc.haltPc ∧ mc.target.getPc ms ≠ mc.ccachePc ∧
      Misc.findIndex (mc.target.getPc ms) mc.ffiEntryPcs 0 = some index ∧
      holEl index mc.ffiNames = .extCall name ∧
      sptAListLookup index mc.mmioInfo = none ∧
      readFfiBytearraysHOL mc ms = (some bytes, some bytes2) ∧
      callFFIHOL ffi (.extCall name) bytes bytes2 = .ret newFfi newBytes) :
    nextInterference mc ffi ms = some
      (.ffiApp index newBytes ms (mc.ffiInterfer 0 (index, newBytes, ms)),
        { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }, newFfi) := by
  apply nextInterferenceIntro mc ffi 1 ms
  rcases h with ⟨hn, hh, hc, hi, he, hm, hr, hf⟩
  simp [findNextInterference, hn, hh, hc, hi, he, hm, hr, hf, applyOracleHOL]

/-- Literal source666: the full guarded cache result and shifted interference oracle. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem nextInterferenceCache {width : Nat} [NeZero width]
    {S Q : Type} {σ : Type} (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (ms : S)
    (h : ¬ (mc.progAddresses (mc.target.getPc ms) ∧ mc.target.getPc ms ∉ mc.ffiEntryPcs) ∧
      mc.target.getPc ms ≠ mc.haltPc ∧ mc.target.getPc ms = mc.ccachePc) :
    nextInterference mc ffi ms = some
      (.ccApp (mc.target.getReg ms mc.ptrReg) (mc.target.getReg ms mc.lenReg) ms
        (mc.ccacheInterfer 0 (mc.target.getReg ms mc.ptrReg, mc.target.getReg ms mc.lenReg, ms)),
        { mc with ccacheInterfer := holShiftSeq 1 mc.ccacheInterfer }, ffi) := by
  apply nextInterferenceIntro mc ffi 1 ms
  rcases h with ⟨hn, hh, hc⟩
  simp only [findNextInterference]
  rw [if_neg hn, if_neg hh, if_pos hc]
  rfl

end Flapjack.Compiler.Backend.Semantics.TargetProps

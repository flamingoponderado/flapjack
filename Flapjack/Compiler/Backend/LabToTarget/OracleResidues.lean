import Flapjack.Compiler.Backend.LabToTarget.OracleTie

/-! Original oracle-tie transport to a shifted machine configuration and the
cache-flush register residues (lab_to_targetProofScript.sml:7453-7524). All
original configuration-field and machine-PC guards are retained; the
residues are derived from the actual next interference, not assumed. -/
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.Semantics.TargetProps

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem oracleTie_shiftGen {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc mc2 : MachineConfig width S Q) (ms1 : S)
    (s1 : Flapjack.Compiler.Backend.LabSem.State width C F) (ms2 : S) (l : Nat)
    (h : oracleTie mc ms1 s1 ∧
      (∀ k, findNextInterference mc s1.ffi (k + l) ms1 =
        findNextInterference mc2 s1.ffi k ms2) ∧
      mc2.target = mc.target ∧ mc2.calleeSavedRegs = mc.calleeSavedRegs ∧
      mc2.ptrReg = mc.ptrReg) :
    oracleTie mc2 ms2 s1 := by
  obtain ⟨ht, hf, htarget, hcallee, hptr⟩ := h
  have hn := nextInterferenceShift mc mc2 s1.ffi s1.ffi ms1 ms2 l hf
  have ho := constructedOraclesEq mc mc2 s1.ffi s1.ffi ms1 ms2
    ⟨hn, htarget.symm, hcallee.symm, hptr.symm⟩
  exact ⟨ht.1.trans ho.1, ht.2.1.trans ho.2.1, ht.2.2.1.trans ho.2.2.1,
    ht.2.2.2.trans ho.2.2.2⟩

-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem oracleTie_ccacheResidues {width : Nat} [NeZero width] {S Q C : Type} {F : Type}
    (mc mc2 : MachineConfig width S Q) (ms1 : S)
    (s1 : Flapjack.Compiler.Backend.LabSem.State width C F) (ms2 : S) (l : Nat)
    (t1 : AsmState width)
    (h : oracleTie mc ms1 s1 ∧
      (∀ k, findNextInterference mc s1.ffi (k + l) ms1 =
        findNextInterference mc2 s1.ffi k ms2) ∧
      mc2.target = mc.target ∧ mc2.ptrReg = mc.ptrReg ∧ mc2.lenReg = mc.lenReg ∧
      mc2.ccacheInterfer = mc.ccacheInterfer ∧
      ¬ (mc2.progAddresses (mc2.target.getPc ms2) ∧
        mc2.target.getPc ms2 ∉ mc2.ffiEntryPcs) ∧
      mc2.target.getPc ms2 ≠ mc2.haltPc ∧ mc2.target.getPc ms2 = mc2.ccachePc) :
    (fun a => getRegValue (s1.ccRegs 0 a) (t1.regs a) id) =
      (fun a => if a ∈ mc.calleeSavedRegs ∨ a = mc.ptrReg ∨
          ¬ a < mc.target.config.regCount ∨ a ∈ mc.target.config.avoidRegs
        then t1.regs a
        else mc.target.getReg (mc.ccacheInterfer 0
          (mc.target.getReg ms2 mc.ptrReg, mc.target.getReg ms2 mc.lenReg, ms2)) a) ∧
    (fun n => s1.ccFpRegs 0 n) =
      (fun n => mc.target.getFpReg (mc.ccacheInterfer 0
        (mc.target.getReg ms2 mc.ptrReg, mc.target.getReg ms2 mc.lenReg, ms2)) n) := by
  obtain ⟨ht, hf, htarget, hptr, hlen, hcc, hnot, hhalt, hpc⟩ := h
  have hn := nextInterferenceShift mc mc2 s1.ffi s1.ffi ms1 ms2 l hf
  have h2 := nextInterferenceCache mc2 s1.ffi ms2 ⟨hnot, hhalt, hpc⟩
  rw [htarget, hptr, hlen, hcc] at h2
  rw [h2] at hn
  obtain ⟨hregs, hfp, -⟩ := oracleTie_cacheStep mc ms1 s1 _ _ _ _ _ _ ⟨ht, hn⟩
  refine ⟨funext fun a => ?_, funext fun n => hfp n⟩
  rw [hregs a]
  split <;> rfl

end Flapjack.Compiler.Backend.LabToTarget

import Flapjack.Compiler.Backend.LabToTarget.Initialization.MemorySeparationCases
namespace Flapjack.Test.LabToTargetInitializerMemorySeparationParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc

-- Actual buffer write candidates cannot match any FFI entry address; every
-- source guard is present, and no desired exclusion is supplied as a premise.
example {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (ffi : HolFfiState F)
    (code code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → Config × LabProgHOL width)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) :
    goodCode mc.target.config (.ln : Spt (Spt Nat)) code ∧ mcConfOk mc ∧
    (noShareMemInst code → compilerOracleOk coracle labs (progToBytes code2).length
      mc.target.config mc.ffiNames) ∧
    listSubset ((findFfiNames code).filter (fun x => match x with
      | .extCall _ => true | _ => false)) (mc.ffiNames.take i) = true ∧
    removeLabels clock mc.target.config 0 .ln (mc.ffiNames.take i) code = some (code2,labs) ∧
    goodInitState mc ms (progToBytes code2) cbspace t m dm sdm ∧
    getShmemInfo code2 0 [] [] = (newFfiNames,shmemInfo) ∧
    newShmemInfo = shmemInfo.map (fun rec => { rec with
      entryPc := (mc.target.getPc ms).toNat + rec.entryPc,
      exitPc := (mc.target.getPc ms).toNat + rec.exitPc }) ∧
    mc.ffiNames.drop i = newFfiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
    newShmemInfo.map ShmemInfoNum.entryPc = (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
    mc.mmioInfo = List.zip ((List.range newShmemInfo.length).map (fun index => index+i))
      (newShmemInfo.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff), rec.reg,
        BitVec.ofNat width rec.exitPc))) ∧
    noInstallOrNoShareMem code mc.ffiNames ∧
    (∀ bn, bn < cbspace → BitVec.ofNat width bn + BitVec.ofNat width (progToBytes code2).length +
      mc.target.getPc ms ∉ mc.ffiEntryPcs.take i) →
    ∀ bn, bn < cbspace → ∀ entry ∈ mc.ffiEntryPcs,
      mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length + BitVec.ofNat width bn ≠ entry := by
  intro h bn hb entry he hEq
  have hc := makeInit_stateRel_memorySeparationCases mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle newFfiNames shmemInfo newShmemInfo h
  dsimp only [makeInit] at hc
  have hx := hc.2 bn (by simpa using hb)
  apply hx
  rw [hEq]
  exact he
end Flapjack.Test.LabToTargetInitializerMemorySeparationParity

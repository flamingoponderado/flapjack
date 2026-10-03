import Flapjack.Compiler.Backend.LabToTarget.Initialization.InterferenceCases
namespace Flapjack.Test.LabToTargetInitializerInterferenceParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc

-- Actual cache-interference return PC is an observed target field derived
-- from the full source guard and original case entry/alignment premises.
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
    ∀ (ms2 : S) (stAsm : AsmState width) (k : Nat) (a1 a2 : BitVec width),
      targetStateRel mc.target
        { stAsm with pc := mc.target.getPc ms - BitVec.ofNat width (2 * ffiOffset) } ms2 ∧
      holAligned mc.target.config.codeAlignment
        (stAsm.regs (match mc.target.config.linkReg with | some n => n | none => 0)) = true →
      mc.target.getPc (mc.ccacheInterfer k (a1,a2,ms2)) =
        stAsm.regs (match mc.target.config.linkReg with | some n => n | none => 0) := by
  intro h ms2 stAsm k a1 a2 hc
  have hs := makeInit_stateRel_interferenceCases mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle newFfiNames shmemInfo newShmemInfo h
  dsimp only [makeInit] at hs
  have hr := hs.2.1 ms2 stAsm k a1 a2 hc
  exact hr.2.1
end Flapjack.Test.LabToTargetInitializerInterferenceParity

import Flapjack.Compiler.Backend.LabToTarget.Initialization.FullStateRel
namespace Flapjack.Test.LabToTargetInitializerFullStateRelParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc
-- A consumer of the whole original relation derives the actual compile
-- interface and byte observations for every source-aligned memory address.
-- It receives no already-initialized relation or desired target output.
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
    let initial := makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle
    ∀ address, initial.memDomain (holByteAlign address) = true →
      initial.compile = compileLab mc.target.config ∧
      t.memDomain address ∧ initial.memDomain address = true ∧
      wordLocValByte (mc.target.getPc ms) labs initial.memory address initial.be = some (t.mem address) := by
  intro h
  dsimp only
  intro address ha
  have hr := makeInit_stateRel mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle newFfiNames shmemInfo newShmemInfo h
  have hc := stateRel_compile mc code2 labs (mc.target.getPc ms) _ t ms hr
  have hm := stateRel_memory mc code2 labs (mc.target.getPc ms) _ t ms hr address ha
  exact ⟨hc,hm⟩
end Flapjack.Test.LabToTargetInitializerFullStateRelParity

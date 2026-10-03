import Flapjack.Compiler.Backend.LabToTarget.Initialization.BasicCases
namespace Flapjack.Test.LabToTargetInitializerBasicCasesParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc

-- Generic native consumer observes actual target memory bytes, initial PC and remaining code-buffer space;
-- the complete source guard supplies every invariant rather than these outputs.
example {width : Nat} [NeZero width] {S Q F : Type}
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
    ∀ a, dm (holByteAlign a) = true →
      wordLocValByte (mc.target.getPc ms) labs m a mc.target.config.bigEndian = some (t.mem a) ∧
      t.pc = mc.target.getPc ms ∧
      (∀ n, n < cbspace →
        let address := mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length + BitVec.ofNat width n
        t.memDomain address ∧ dm address ≠ true) := by
  intro h a ha
  have hc := makeInit_stateRel_basicCases mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle newFfiNames shmemInfo newShmemInfo h
  dsimp only [makeInit] at hc
  obtain ⟨_,_,_,_,hmemory,hbufferSpace,_,hpc,_,_⟩ := hc
  have he := removeLabels_correct clock mc.target.config 0 .ln (mc.ffiNames.take i) code code2 labs
  obtain ⟨hends,hlabels,hids,hdistinct,hdis,hsub,hpre⟩ := h.1
  have hr := he ⟨h.2.2.2.2.1,h.2.1.2.2.2.2.2.2.2,hends,hlabels,hids,hdistinct,hdis,hsub,hpre,
    by decide,by simp [labLookup,sptLookup]⟩
  have hz := posVal_zero code2 mc.target.config labs (mc.ffiNames.take i) 0 hr.1
  refine ⟨(hmemory a ha).2.2,by simpa [hz] using hpc,?_⟩
  intro n hn
  simpa only [List.length_nil,Nat.zero_add] using hbufferSpace n hn

end Flapjack.Test.LabToTargetInitializerBasicCasesParity

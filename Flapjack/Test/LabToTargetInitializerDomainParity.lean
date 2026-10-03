import Flapjack.Compiler.Backend.LabToTarget.Initialization.DomainCodeCase
namespace Flapjack.Test.LabToTargetInitializerDomainParity
open Flapjack Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc
-- The actual shared-fetch descriptor has a valid full FFI index, and every
-- nonshared fetched byte is disjoint from every full FFI entry. Neither
-- desired observation is supplied as a premise.
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
    (∀ pc op reg addr bytes len,
      asmFetchAux pc code2 = some (.asm (.shareMem op reg addr) bytes len) →
      ∃ index, i ≤ index ∧ index < mc.ffiNames.length ∧
        findIndex (mc.target.getPc ms + BitVec.ofNat width (posVal pc 0 code2))
          mc.ffiEntryPcs 0 = some index ∧
        holEl index mc.ffiNames = .sharedMem (getMemopInfo op).1 ∧
        mc.mmioInfo.lookup index = some ((getMemopInfo op).2,addr,reg,
          mc.target.getPc ms+BitVec.ofNat width (posVal pc 0 code2+len))) ∧
    (∀ pc line, asmFetchAux pc code2 = some line →
      (∀ op reg addr bytes len, line ≠ .asm (.shareMem op reg addr) bytes len) →
      ∀ a, a < (lineBytes line).length →
        mc.target.getPc ms + BitVec.ofNat width a + BitVec.ofNat width (posVal pc 0 code2)
          ∉ mc.ffiEntryPcs) := by
  intro h
  have hc := makeInit_stateRel_domainCodeCase mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle newFfiNames shmemInfo newShmemInfo h
  obtain ⟨hgood,hmc,horacle,hffis,hremove,hinit,hinfo,hoff,hdrop,hboundary,hentries,hmmio,hsafe,hbuffer⟩ := h
  have hl := startPcOk_lengths hinit.2.2.2.1
  constructor
  · intro pc op reg addr bytes len hf
    obtain ⟨index,hlo,hsearch,hname,hdescriptor⟩ := hc.1 pc op reg addr bytes len i ⟨hf,hboundary⟩
    have hb := (findIndexLessLength _ _ 0 index hsearch).2
    refine ⟨index,hlo,by simpa only [Nat.zero_add,←hl] using hb,hsearch,?_,?_⟩
    · simpa only [getMemopInfo] using hname
    · simpa only [getMemopInfo] using hdescriptor
  · intro pc line hf hn a ha hmem
    exact hc.2.1 pc line ⟨hf,hn⟩ _ hmem ⟨a,rfl,ha⟩
end Flapjack.Test.LabToTargetInitializerDomainParity

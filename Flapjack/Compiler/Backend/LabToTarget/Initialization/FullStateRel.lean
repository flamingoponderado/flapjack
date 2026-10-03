import Flapjack.Compiler.Backend.LabToTarget.Initialization.BasicCases
import Flapjack.Compiler.Backend.LabToTarget.Initialization.InterferenceCases
import Flapjack.Compiler.Backend.LabToTarget.Initialization.MemorySeparationCases
import Flapjack.Compiler.Backend.LabToTarget.Initialization.DomainCodeCase
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm Flapjack.Misc
/-- Full original initializer relation: complete seventeen-case assembly,
all original binders/fourteen guards and the whole actual stateRel conclusion.
No target relation or case proof is supplied by the caller. The original
independent gamma value type occurs only in the literal empty goodCode label
tree; its two domains are empty. The statement retains that arbitrary type G;
the proof specializes only its internal empty-tree support lemmas to Nat. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "IMP_state_rel_make_init" (words_as_type_indexed_bitvec)]
theorem makeInit_stateRel {width : Nat} [NeZero width] {S Q G : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (ffi : HolFfiState F)
    (code code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → Config × LabProgHOL width)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) :
    goodCode mc.target.config (.ln : Spt (Spt G)) code ∧ mcConfOk mc ∧
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
    stateRel (mc,code2,labs,mc.target.getPc ms) initial t ms := by
  intro h
  have hgoodNat : goodCode mc.target.config (.ln : Spt (Spt Nat)) code := by
    have hd : Set.ofPred (sptDomain (.ln : Spt (Spt G))) =
        Set.ofPred (sptDomain (.ln : Spt (Spt Nat))) := by
      ext key
      simp [sptDomain, sptLookup]
    simpa only [goodCode, labsDomain_ln, hd] using h.1
  have h := And.intro hgoodNat h.2
  have hb := makeInit_stateRel_basicCases mc ms ffi code code2 labs clock i cbspace t m dm sdm coracle newFfiNames shmemInfo newShmemInfo h
  have hf := makeInit_stateRel_interferenceCases mc ms ffi code code2 labs clock i cbspace t m dm sdm coracle newFfiNames shmemInfo newShmemInfo h
  have hm := makeInit_stateRel_memorySeparationCases mc ms ffi code code2 labs clock i cbspace t m dm sdm coracle newFfiNames shmemInfo newShmemInfo h
  have hd := makeInit_stateRel_domainCodeCase mc ms ffi code code2 labs clock i cbspace t m dm sdm coracle newFfiNames shmemInfo newShmemInfo h
  obtain ⟨hor,hlabelsEven,hnames,hbytesEven,hmemory,hspace',hbufferBytes,hpc',hsections,hsafety⟩ := hb
  obtain ⟨hffi',hcache',hnameLayout,hshareState⟩ := hf
  obtain ⟨hmmioDomain,hbufferSep⟩ := hm
  obtain ⟨hgood,hmc,horacle,hffis,hremove,hinit,hinfo,hoff,hdrop,hboundary,hentries,hmmio,hsafe,hbuffer⟩ := h
  obtain ⟨hends,hlabels,hids,hdistinct,hdis,hsub,hpre⟩ := hgood
  have hr := removeLabels_correct clock mc.target.config 0 .ln (mc.ffiNames.take i) code code2 labs
  have hresult := hr ⟨hremove,hmc.2.2.2.2.2.2.2,hends,hlabels,hids,hdistinct,hdis,hsub,hpre,by decide,
    by simp [labLookup,sptLookup]⟩
  obtain ⟨henc,hsim,hodd,heven,hpreserve,hlookup⟩ := hresult
  obtain ⟨hrel,hconfigured,hpc,hstart,halign,hinter,hffi,hcache,hloaded,hbytes,hdom,hclosed,hshared,
    hshClosed,hdisjoint,hword,hspace,hsize⟩ := hinit
  obtain ⟨hfailed,hbe,hta,htdomain,hlr⟩ := hconfigured
  obtain ⟨hdim,hencoder,hptr,hlen,hptr2,hlen2,hlink,hencc⟩ := hmc
  rw [hpc] at hstart
  obtain ⟨hhalt,hccache,hshalt,hsccache,hhaltPc,hccachePc,hbit,j,hj,hprefix,hsuffix,hlength⟩ := hstart
  dsimp only [stateRel]
  refine ⟨hrel,hdim,htdomain.symm,hhalt,hccache,hptr,rfl,hlen,rfl,hptr2,rfl,hlen2,rfl,
    by cases hl : mc.target.config.linkReg <;> simpa only [makeInit,hl] using hlink,hmmioDomain,hffi',hcache',rfl,hor,hlabelsEven,hbit,hnames,
    hbytesEven,hnameLayout,hhaltPc,hccachePc,?_,hlookup,?_,?_,hmemory,hspace',?_,rfl,hbufferBytes,
    ?_,hbufferSep,rfl,hfailed,?_,hpc',?_,hlr,hbe,hta,hencc,?_,hsections,hsim,hshareState,hd,hlength,hsafety⟩
  · simpa only [htdomain] using hinter
  · intro r; rfl
  · intro r; rfl
  · simpa only [makeInit,hpc] using hbytes
  · simpa only [makeInit,List.length_nil,Nat.add_zero,Nat.zero_add,Nat.add_comm] using hsize
  · exact hbe.symm
  · simpa only [BitVec.and_comm,hpc] using halign
  · simpa only [hboundary,holThe] using henc
end Flapjack.Compiler.Backend.LabToTarget

import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.Compiler.Backend.LabToTarget.StateRel
import Flapjack.Compiler.Backend.Semantics.TargetSem.InitializationContracts
import Flapjack.Compiler.Backend.Semantics.TargetProps.PostInterferenceState
import Flapjack.Compiler.Backend.LabToTarget.MmioClassification
import Flapjack.Misc.FindIndex.Membership
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm Flapjack.Misc
open Flapjack.Compiler.Backend.Semantics.TargetProps
private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩
-- Flapjack infrastructure: both Nat-key list lookups retain first-match
-- behavior, including duplicate keys; this is not a new HOL declaration.
private theorem initializer_alookup_eq_lookup {α : Type} (key : Nat) (entries : List (Nat × α)) :
    sptAListLookup key entries = entries.lookup key := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rcases entry with ⟨k,value⟩
    by_cases h : key = k
    · simp [sptAListLookup,List.lookup,h]
    · cases hb : (key == k) with
      | false => simp [sptAListLookup,List.lookup,h,hb,ih]
      | true => exact False.elim (h (by simpa only [beq_iff_eq] using hb))

/-- Four genuine full initializer cases: ISR2 normal FFI, ISR3 cache clear,
ISR8 external-name/search layout, and ISR15 shared-memory interference. All
original fourteen guards and binders remain, and the actual makeInit state
appears in the complete original relation clauses. Source boundary/length
facts discharge every name/entry bound; no past-end EL or extra output premise
is used. This is not the full seventeen-case assembling theorem. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem makeInit_stateRel_interferenceCases {width : Nat} [NeZero width] {S Q : Type} {F : Type}
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
(∀ (ms2 : S) (k index : Nat) (newBytes : List (BitVec 8)) (t : AsmState width)
      (bytes bytes2 : List (BitVec 8)) (st newSt : HolFfiState F) (i : Nat),
    mmioPcsMinIndex mc.ffiNames = some i ∧ index < i ∧
    readFfiBytearraysHOL mc ms2 = (some bytes, some bytes2) ∧
    Relation.ReflTransGen callFFIRelHOL initial.ffi st ∧
    callFFIHOL st (holEl index mc.ffiNames) bytes bytes2 = .ret newSt newBytes ∧
    mc.progAddresses = t.memDomain ∧
    targetStateRel mc.target { t with pc := (mc.target.getPc ms) - BitVec.ofNat width ((3 + index) * ffiOffset) } ms2 ∧
    holAligned mc.target.config.codeAlignment (t.regs initial.linkReg) = true →
    let ms' := mc.ffiInterfer k (index, newBytes, ms2)
    targetStateRel mc.target
      { t with
        regs := fun a => if a ∈ mc.calleeSavedRegs ∨ ¬ a < mc.target.config.regCount ∨
            a ∈ mc.target.config.avoidRegs then t.regs a else mc.target.getReg ms' a
        fpRegs := fun n => mc.target.getFpReg ms' n
        mem := asmWriteBytearrayHOL (t.regs initial.ptr2Reg) newBytes t.mem
        pc := t.regs initial.linkReg } ms') ∧
  (∀ (ms2 : S) (t : AsmState width) (k : Nat) (a1 a2 : BitVec width),
    targetStateRel mc.target { t with pc := (mc.target.getPc ms) - BitVec.ofNat width (2 * ffiOffset) } ms2 ∧
    holAligned mc.target.config.codeAlignment (t.regs initial.linkReg) = true →
    let ms' := mc.ccacheInterfer k (a1, a2, ms2)
    targetStateRel mc.target
      { t with
        regs := fun a => if a ∈ mc.calleeSavedRegs ∨ a = initial.ptrReg ∨
            ¬ a < mc.target.config.regCount ∨ a ∈ mc.target.config.avoidRegs
            then t.regs a else mc.target.getReg ms' a
        fpRegs := fun n => mc.target.getFpReg ms' n
        pc := t.regs initial.linkReg } ms') ∧
(∀ name i, name ∈ mc.ffiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
    getFfiIndex mc.ffiNames name < i →
    (∃ name', name = HolFfiName.extCall name') ∧
    ¬ mc.progAddresses ((mc.target.getPc ms) - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames name) * ffiOffset)) ∧
    (mc.target.getPc ms) - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames name) * ffiOffset) ≠ mc.haltPc ∧
    (mc.target.getPc ms) - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames name) * ffiOffset) ≠ mc.ccachePc ∧
    findIndex ((mc.target.getPc ms) - BitVec.ofNat width ((3 + getFfiIndex mc.ffiNames name) * ffiOffset))
      mc.ffiEntryPcs 0 = some (getFfiIndex mc.ffiNames name)) ∧
    shareMemStateRel mc initial t ms := by
  rintro ⟨hgood,hmc,horacle,hffis,hremove,hinit,hinfo,hoff,hdrop,hboundary,hentries,hmmio,hsafe,hbuffer⟩
  obtain ⟨hrel,hconfigured,hpc,hstart,halign,hinter,hffi,hcache,hloaded,hbytes,hdom,hclosed,hshared,
    hshClosed,hdisjoint,hword,hspace,hsize⟩ := hinit
  rw [hpc] at hffi hcache hstart
  obtain ⟨hhalt,hccache,hshalt,hsccache,hhaltPc,hccachePc,hbit,j,hj,hprefix,hsuffix,hlength⟩ := hstart
  have hjEq : j = i := Option.some.inj (hj.symm.trans hboundary)
  subst j
  obtain ⟨hbound,hpre,hsuf⟩ := mmioPcsMinIndex_isSome mc.ffiNames i hboundary
  dsimp only [makeInit]
  refine ⟨?_,?_,?_,?_⟩
  · intro ms2 k index newBytes stAsm bytes bytes2 st newSt i' ⟨hidx,hlt,hread,hsteps,hcall,hd,hrel,ha⟩
    have hii : i' = i := Option.some.inj (hidx.symm.trans hboundary)
    subst i'
    have hlen := callFFIHOL_ret_length st (holEl index mc.ffiNames) bytes bytes2 newBytes newSt hcall
    have he : holEl index mc.ffiNames = .extCall (.implode []) → newBytes = bytes2 := by
      intro hn
      simp [callFFIHOL,hn] at hcall
      exact hcall.2.symm
    have hpost := ffiInterferOkPostFfiAsm (mc.target.getPc ms) mc index i k stAsm ms2 bytes bytes2 newBytes
      ⟨hffi,by omega,hboundary,hlt,hd,hread,hlen,he,
        by simpa only [BitVec.sub_eq_add_neg,BitVec.add_comm] using hrel,by cases hl : mc.target.config.linkReg <;> simpa [hl] using ha⟩
    cases hl : mc.target.config.linkReg <;>
      simpa only [postFfiAsmHOL,Bool.or_eq_true,List.contains_iff_mem,decide_eq_true_eq,or_assoc,hl] using hpost
  · intro ms2 stAsm k a1 a2 ⟨hr,ha⟩
    have hp := ccacheInterferOkPostCcacheAsm (mc.target.getPc ms) mc stAsm ms2 k a1 a2
      ⟨hcache,by simpa only [BitVec.sub_eq_add_neg,BitVec.add_comm] using hr,by cases hl : mc.target.config.linkReg <;> simpa [hl] using ha⟩
    cases hl : mc.target.config.linkReg <;>
      simpa only [postCcacheAsmHOL,Bool.or_eq_true,List.contains_iff_mem,decide_eq_true_eq,or_assoc,hl] using hp
  · intro name idx ⟨hn,hidx,hi⟩
    have hEq : idx = i := Option.some.inj (hidx.symm.trans hboundary)
    subst idx
    obtain ⟨n,hs,hb,hv⟩ := findIndex_mem mc.ffiNames name 0 hn
    have hnEq : getFfiIndex mc.ffiNames name = n := by simp [getFfiIndex,hs]
    rw [hnEq] at hi ⊢
    obtain ⟨name',he⟩ := hpre n hi
    obtain ⟨hd,_,hh,hc,hf⟩ := hprefix n hi
    exact ⟨⟨name',hv.symm.trans he⟩,hd,hh,hc,hf⟩
  · constructor
    · intro ms2 k index newBytes stAsm nb ad offs re pc' ad' st newSt idx
        ⟨hidx,hlo,hhi,hsteps,hm,hd,had,hr⟩
      have hEq : idx = i := Option.some.inj (hidx.symm.trans hboundary)
      subst idx
      obtain ⟨op,hname⟩ := hsuf index ⟨hlo,hhi⟩
      obtain ⟨info,hinfo,hread,hwrite⟩ := (hffi ms2 k index newBytes stAsm [] [] i ⟨hhi,hboundary,hd⟩).2 ⟨hlo,hr⟩
      have hi : info = (nb,HolAddr.addr ad offs,re,pc') := by
        have hlookup : sptAListLookup index mc.mmioInfo = some (nb,HolAddr.addr ad offs,re,pc') := by
          simpa only [initializer_alookup_eq_lookup] using hm
        exact Option.some.inj (hinfo.symm.trans hlookup)
      subst info
      refine ⟨op,hname,?_⟩
      cases op with
      | mappedRead =>
        intro _
        exact hread hname newBytes
      | mappedWrite =>
        intro _
        exact hwrite hname
    · intro index idx ⟨hidx,hhi,hlo⟩
      have hEq : idx = i := Option.some.inj (hidx.symm.trans hboundary)
      subst idx
      exact hsuffix index ⟨hhi,hlo⟩
end Flapjack.Compiler.Backend.LabToTarget

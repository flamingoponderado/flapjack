import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.Compiler.Backend.LabToTarget.StateRel
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabelsCorrectness
import Flapjack.Compiler.Backend.Semantics.TargetSem.InitializationContracts
import Flapjack.Compiler.Backend.LabToTarget.ShmemEntryMax
import Flapjack.Compiler.Backend.LabToTarget.MmioClassification
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm Flapjack.Misc
/-- Flapjack word-addition infrastructure for the literal buffer address;
this is not a separately named HOL declaration. -/
private theorem wordAdd_left_comm {width : Nat} (a b c : BitVec width) : a + (b+c) = b+(a+c) := by
  rw [←BitVec.add_assoc,BitVec.add_comm a b,BitVec.add_assoc]
/-- Original full initializer ISR1 MMIO lookup and ISR12 buffer separation.
Every original binder and fourteen guards remain. The whole source lookup
domain/existence condition and actual makeInit buffer exclusion are proved.
DROP entries come from the original extraction and accepted strict entry bound;
canonical words cancel the initial PC with only the original size guard.
No EL, default, target exclusion or additional successful search is assumed. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "IMP_state_rel_make_init" (words_as_type_indexed_bitvec)]
theorem makeInit_stateRel_memorySeparationCases {width : Nat} [NeZero width] {S Q : Type} {F : Type}
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
    (∃ j, mmioPcsMinIndex mc.ffiNames = some j ∧
      ∀ index, if j ≤ index ∧ index < mc.ffiNames.length then
        ∃ info, mc.mmioInfo.lookup index = some info else mc.mmioInfo.lookup index = none) ∧
    (∀ bn, bn < initial.codeBuffer.buffer.length + initial.codeBuffer.spaceLeft →
      initial.codeBuffer.position + BitVec.ofNat width bn ∉ mc.ffiEntryPcs) := by
  rintro ⟨hgood,hmc,horacle,hffis,hremove,hinit,hinfo,hoff,hdrop,hboundary,hentries,hmmio,hsafe,hbuffer⟩
  obtain ⟨hends,hlabels,hids,hdistinct,hdis,hsub,hpre⟩ := hgood
  have hr := removeLabels_correct clock mc.target.config 0 .ln (mc.ffiNames.take i) code code2 labs
  have hresult := hr ⟨hremove,hmc.2.2.2.2.2.2.2,hends,hlabels,hids,hdistinct,hdis,hsub,hpre,by decide,
    by simp [labLookup,sptLookup]⟩
  have henc := hresult.1
  have hencc := hmc.2.2.2.2.2.2.2
  obtain ⟨hrel,hconfigured,hpc,hstart,halign,hinter,hffi,hcache,hloaded,hbytes,hdom,hclosed,hshared,
    hshClosed,hdisjoint,hword,hspace,hsize⟩ := hinit
  have hlength := startPcOk_lengths hstart
  have hbound := (mmioPcsMinIndex_isSome mc.ffiNames i hboundary).1
  have hlen : newShmemInfo.length = mc.ffiNames.length-i := by
    have he := congrArg List.length hentries
    simpa only [List.length_map,List.length_drop,←hlength] using he
  have hkeys : mc.mmioInfo.map Prod.fst = (List.range newShmemInfo.length).map (fun index => index+i) := by
    rw [hmmio,List.map_fst_zip (by simp)]
  have hmemKeys : ∀ index, index ∈ mc.mmioInfo.map Prod.fst ↔ i ≤ index ∧ index < mc.ffiNames.length := by
    intro index
    rw [hkeys]
    simp only [List.mem_map,List.mem_range]
    constructor
    · rintro ⟨n,hn,rfl⟩
      omega
    · intro ⟨hlo,hhi⟩
      exact ⟨index-i,by omega,by omega⟩
  let entries := ((List.range (numPcs code2)).map
    (fun pc => lineToInfo code2 0 (pc,asmFetchAux pc code2))).flatten
  have hdata : shmemInfo = entries.map Prod.snd := by
    have hc := getShmemInfo_characterization code2 0 [] [] 0 mc.target.config labs (mc.ffiNames.take i) henc
    have he := congrArg Prod.snd (hinfo.symm.trans hc)
    simpa only [List.nil_append,List.unzip_eq_map,List.map_map,Function.comp_def] using he
  have hmax : ∀ rec ∈ shmemInfo, rec.entryPc < (progToBytes code2).length := by
    intro rec hm
    rw [hdata] at hm
    obtain ⟨entry,he,heq⟩ := List.mem_map.mp hm
    subst rec
    have hx := genlistLineToInfo_entryPcMax mc.target.config labs (mc.ffiNames.take i) 0 code2 ⟨henc,hencc⟩ entry he
    simpa only [posVal_numPcs mc.target.config labs (mc.ffiNames.take i) 0 code2 0 henc,Nat.zero_add] using hx
  have hdropMap : newShmemInfo.map ShmemInfoNum.entryPc = (mc.ffiEntryPcs.drop i).map BitVec.toNat := by
    simpa only [List.map_drop] using hentries
  dsimp only [makeInit]
  constructor
  · refine ⟨i,hboundary,?_⟩
    intro index
    split
    · rename_i hidx
      have hm := (hmemKeys index).mpr hidx
      obtain ⟨entry,he,hkey⟩ := List.mem_map.mp hm
      have hs : (mc.mmioInfo.lookup index).isSome := List.lookup_isSome_iff.mpr
        ⟨entry,he,by simpa only [beq_iff_eq] using hkey.symm⟩
      exact Option.isSome_iff_exists.mp hs
    · rename_i hidx
      simp only [List.lookup_eq_none_iff,bne_iff_ne]
      intro entry he hkey
      apply hidx
      apply (hmemKeys index).mp
      exact List.mem_map.mpr ⟨entry,he,hkey.symm⟩
  · intro bn hb hmem
    have hbn : bn < cbspace := by simpa using hb
    have hpart : mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length + BitVec.ofNat width bn ∈
        mc.ffiEntryPcs.take i ++ mc.ffiEntryPcs.drop i := by simpa only [List.take_append_drop] using hmem
    rcases List.mem_append.mp hpart with hp | hs
    · apply hbuffer bn hbn
      simpa only [BitVec.add_assoc,BitVec.add_comm,wordAdd_left_comm] using hp
    · have hNat : (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length +
          BitVec.ofNat width bn).toNat ∈ (mc.ffiEntryPcs.drop i).map BitVec.toNat :=
        List.mem_map.mpr ⟨_,hs,rfl⟩
      rw [←hdropMap] at hNat
      obtain ⟨updated,hu,he⟩ := List.mem_map.mp hNat
      rw [hoff] at hu
      obtain ⟨rec,hrec,huEq⟩ := List.mem_map.mp hu
      subst updated
      have hm := hmax rec hrec
      have hv := congrArg (BitVec.ofNat width) he
      simp only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at hv
      have hEq : BitVec.ofNat width ((progToBytes code2).length+bn) = BitVec.ofNat width rec.entryPc := by
        apply (BitVec.add_right_inj (mc.target.getPc ms)).mp
        simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hv.symm
      have hNatEq := congrArg BitVec.toNat hEq
      have hsum : (progToBytes code2).length+bn < 2^width := by omega
      have hrecBound : rec.entryPc < 2^width := by omega
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hsum,Nat.mod_eq_of_lt hrecBound] at hNatEq
      omega
end Flapjack.Compiler.Backend.LabToTarget

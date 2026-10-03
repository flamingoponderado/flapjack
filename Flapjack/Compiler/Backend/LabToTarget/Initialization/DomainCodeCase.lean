import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.Compiler.Backend.LabToTarget.StateRel
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabelsCorrectness
import Flapjack.Compiler.Backend.Semantics.TargetSem.InitializationContracts
import Flapjack.Compiler.Backend.LabToTarget.ShmemOffset
import Flapjack.Compiler.Backend.LabToTarget.ShmemPrefix
import Flapjack.Compiler.Backend.LabToTarget.ShmemCorrectness
import Flapjack.Compiler.Backend.LabToTarget.FfiEntryExclusion
import Flapjack.Compiler.Backend.LabToTarget.WordSearch
import Flapjack.Misc.FindIndex.Shift
import Flapjack.Misc.FindIndex.Append
import Flapjack.Misc.FindIndex.Bounds
import Mathlib.Data.List.Nodup
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm Flapjack.Misc
/-- Flapjack proof infrastructure combining the original reviewed offset and
prefix laws. No separately named HOL declaration; this is the precise extraction
premise needed inside original initializer ISR16, without adding an output guard. -/
private theorem initializer_extractionOffset {width : Nat} [NeZero width]
 (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (validFfis ffis : List HolFfiName)
 (code : LabProgHOL width) (p i : Nat) (names : List HolFfiName)
 (records shifted : List ShmemInfoNum)
 (he : allEncOk c labs validFfis 0 code)
 (hout : getShmemInfo code 0 [] [] = (names,records))
 (hoff : shifted = records.map (fun r => {r with entryPc:=p+r.entryPc,exitPc:=p+r.exitPc}))
 (hdrop : ffis.drop i = names) :
 getShmemInfo code p (ffis.take i) [] = (ffis,shifted) := by
 have ho := getShmemInfo_initPcOffset c labs validFfis 0 code p he
 have hn : (getShmemInfo code p [] []).1 = names := by
   rw [←ho.1,hout]
 have hr : (getShmemInfo code p [] []).2 = shifted := by
   rw [←ho.2,hout]
   exact hoff.symm
 have hp := getShmemInfo_prepend code p (ffis.take i) []
   (getShmemInfo code p (ffis.take i) []).1
   (getShmemInfo code p (ffis.take i) []).2 rfl
 apply Prod.ext
 · rw [hp.1,hn,←hdrop,List.take_append_drop]
 · simpa only [List.nil_append] using hp.2.trans hr

/-- Flapjack infrastructure: unique numeric keys make membership sufficient
for the original first-match association-list lookup; no separate HOL original. -/
private theorem initializer_lookup_mem {B : Type} (values : List (Nat × B))
    (key : Nat) (value : B) (hu : (values.map Prod.fst).Nodup)
    (hm : (key,value) ∈ values) : values.lookup key = some value := by
  induction values with
  | nil => simp at hm
  | cons head tail ih =>
    rcases head with ⟨hk,hv⟩
    have hn := List.nodup_cons.mp hu
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      simp
    · have hneq : key ≠ hk := by
        intro he
        apply hn.1
        exact List.mem_map.mpr ⟨(key,value),hm,he⟩
      have hb : (key == hk) = false := by simpa using hneq
      rw [List.lookup_cons,hb]
      exact ih hn.2 hm

/-- Flapjack infrastructure for original ZIP/GENLIST descriptor lookup under
its source successful-search bound; no separately named HOL declaration. -/
private theorem initializer_indexedLookup {B : Type} (values : List B) (i j : Nat)
    (hj : j < values.length) :
    (List.zip ((List.range values.length).map (fun n => n+i)) values).lookup (j+i) =
      some values[j] := by
  apply initializer_lookup_mem
  · rw [List.map_fst_zip (by simp)]
    rw [List.nodup_map_iff (by intro a b h; exact Nat.add_right_cancel h)]
    exact List.nodup_range
  · apply List.mem_iff_getElem.mpr
    refine ⟨j,by simp [hj],?_⟩
    simp [List.getElem_zip]

/-- Flapjack word arithmetic infrastructure: a small nonnegative increment
whose result is at least the starting word did not wrap. No HOL port tag. -/
private theorem initializer_wordAdd_noWrap {width : Nat} (p : BitVec width)
    (offset : Nat) (hoff : offset < 2^width)
    (hlo : p.toNat ≤ (p + BitVec.ofNat width offset).toNat) :
    p.toNat+offset < 2^width := by
  have hp := p.isLt
  simp only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hoff] at hlo
  by_contra hn
  have hge : 2^width ≤ p.toNat+offset := by omega
  have hmod : (p.toNat+offset) % 2^width = p.toNat+offset-2^width := by
    rw [Nat.mod_eq_sub_mod hge]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hmod] at hlo
  omega

/-- Full original initializer ISR16: the entire shared-memory code domain
relation for actual makeInit, with all original binders and fourteen guards.
All successful searches, valid list accesses and descriptor facts are derived
inside the case; no extra bounds or target-domain premises are supplied. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "IMP_state_rel_make_init" (words_as_type_indexed_bitvec)]
theorem makeInit_stateRel_domainCodeCase {width : Nat} [NeZero width] {S Q : Type} {F : Type}
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
    shareMemDomainCodeRel mc (mc.target.getPc ms) code2
      (fun a => initial.sharedMemDomain a = true) := by
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
  rw [hpc] at hstart
  obtain ⟨hh,hc,hsh,hsc,hha,hca,hbit,i0,hi0,hprefix,hsuffix,hnameLen⟩ := hstart
  have hi0Eq : i0 = i := Option.some.inj (hi0.symm.trans hboundary)
  subst i0
  have hprefix' : ∀ index, index < i →
      ¬ mc.progAddresses (-BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms) ∧
      ¬ mc.sharedAddresses (-BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms) ∧
      -BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms ≠ mc.haltPc ∧
      -BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms ≠ mc.ccachePc ∧
      findIndex (-BitVec.ofNat width (ffiOffset*(index+3)) + mc.target.getPc ms)
        mc.ffiEntryPcs 0 = some index := by
    intro index hi
    simpa only [BitVec.sub_eq_add_neg,BitVec.add_comm,Nat.add_comm,Nat.mul_comm] using hprefix index hi
  have hbytes' : bytesInMemHOL (mc.target.getPc ms) (progToBytes code2) t.mem mc.progAddresses
      (fun a => dm a = true) := by
    simpa only [hpc,hconfigured.2.2.2.1] using hbytes
  have hexclude : ∀ a line pc, asmFetchAux pc code2 = some line → a < (lineBytes line).length →
      mc.target.getPc ms + BitVec.ofNat width a + BitVec.ofNat width (posVal pc 0 code2)
        ∉ mc.ffiEntryPcs.take i := by
    intro a line pc hf ha
    exact asmFetch_notFfiEntryPcs a line pc (fun a => dm a = true) t ms
      (mc.ffiNames.take i) labs i mc code2
      ⟨by omega,hboundary,hlength,henc,hencc,hprefix',hbytes',hf,ha⟩
  have hbound := (mmioPcsMinIndex_isSome mc.ffiNames i hboundary).1
  have hlen : newShmemInfo.length = mc.ffiNames.length-i := by
    have he := congrArg List.length hentries
    simpa only [List.length_map,List.length_drop,←hlength] using he
  have hprefixExternal : ∀ x ∈ mc.ffiNames.take i, ∃ name, x = HolFfiName.extCall name := by
    intro x hx
    obtain ⟨j,hj,hv⟩ := List.mem_take_iff_getElem.mp hx
    have hjlt : j < i := by omega
    obtain ⟨name,hn⟩ := (mmioPcsMinIndex_isSome mc.ffiNames i hboundary).2.1 j hjlt
    refine ⟨name,?_⟩
    exact hv.symm.trans ((holEl_eq_getElem j mc.ffiNames (by omega)).symm.trans hn)
  have hget := initializer_extractionOffset mc.target.config labs (mc.ffiNames.take i) mc.ffiNames
    code2 (mc.target.getPc ms).toNat i newFfiNames shmemInfo newShmemInfo henc hinfo hoff hdrop
  have hsizeBytes : (progToBytes code2).length < 2^width := by omega
  have hok := getShmemInfo_ok mc.target.config labs (mc.ffiNames.take i) 0 code2
    (mc.ffiNames.take i) (mc.target.getPc ms).toNat mc.ffiNames newShmemInfo
    ⟨henc,hencc,hsizeBytes,hprefixExternal,hget⟩
  dsimp only [makeInit]
  refine ⟨?_,?_,hshClosed,hshared.symm⟩
  · intro pc op reg addr bytes len i' ⟨hf,hboundary'⟩
    have hii : i' = i := Option.some.inj (hboundary'.symm.trans hboundary)
    subst i'
    obtain ⟨j,hs,hname,hrecord⟩ := hok.1 pc op reg addr bytes len i ⟨hf,hboundary⟩
    have hj := (findIndexLessLength _ _ 0 j hs).2
    simp only [List.length_map,Nat.zero_add] at hj
    have hmem := findIndex_isMem _ _ 0 j hs
    rw [hentries,←List.map_drop] at hmem
    obtain ⟨w,hw,hew⟩ := List.mem_map.mp hmem
    have hnatbound : (mc.target.getPc ms).toNat + posVal pc 0 code2 < 2^width := by
      rw [←hew]
      exact w.isLt
    have hposbound : posVal pc 0 code2 < 2^width := by omega
    have hsearch : findIndex (mc.target.getPc ms + BitVec.ofNat width (posVal pc 0 code2))
        (mc.ffiEntryPcs.drop i) 0 = some j := by
      rw [←findIndex_mapToNat,List.map_drop,←hentries]
      simpa only [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt hposbound,
        Nat.mod_eq_of_lt hnatbound] using hs
    have hvalid := allEncOk_fetch_lineOk mc.target.config labs (mc.ffiNames.take i) pc 0 code2 _ ⟨henc,hf⟩
    have hpositive : 0 < bytes.length := by
      obtain ⟨count,hbytesEq⟩ := (encWithNop_iff mc.target.config.encode (cbwToAsmHOL (.shareMem op reg addr)) bytes).mp hvalid.1
      have hp := encOk_lengthPositive mc.target.config (cbwToAsmHOL (.shareMem op reg addr)) hencc
      rw [hbytesEq,List.length_append]
      omega
    have hnot : mc.target.getPc ms + BitVec.ofNat width (posVal pc 0 code2)
        ∉ mc.ffiEntryPcs.take i := by
      simpa only [lineBytes,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using hexclude 0 _ pc hf hpositive
    have hnone : findIndex (mc.target.getPc ms + BitVec.ofNat width (posVal pc 0 code2))
        (mc.ffiEntryPcs.take i) 0 = none := by
      cases hs' : findIndex (mc.target.getPc ms + BitVec.ofNat width (posVal pc 0 code2))
          (mc.ffiEntryPcs.take i) 0 with
      | none => rfl
      | some idx => exact False.elim (hnot (findIndex_isMem _ _ 0 idx hs'))
    have htakeLen : (mc.ffiEntryPcs.take i).length = i := by simp only [List.length_take]; omega
    have hshift := (findIndexShift _ _ 0 j hsearch).2 i
    have hfull : findIndex (mc.target.getPc ms + BitVec.ofNat width (posVal pc 0 code2))
        mc.ffiEntryPcs 0 = some (j+i) := by
      rw [←List.take_append_drop i mc.ffiEntryPcs,findIndexAppend,hnone,htakeLen,Nat.zero_add]
      simpa only [Nat.sub_zero] using hshift
    refine ⟨j+i,by omega,hfull,hname,?_⟩
    rw [hmmio]
    have hl := initializer_indexedLookup (newShmemInfo.map (fun rec => (rec.nbytes,
      HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff),rec.reg,
      BitVec.ofNat width rec.exitPc))) i j (by simpa only [List.length_map] using hj)
    simp only [List.length_map] at hl
    rw [hl]
    have hr : newShmemInfo[j] =
        {entryPc:=(newShmemInfo[j]).entryPc,nbytes:=(getMemopInfo op).2,
         addrReg:=match addr with | .addr base _ => base,
         addrOff:=match addr with | .addr _ off => off.toNat,
         reg:=reg,exitPc:=(mc.target.getPc ms).toNat+(posVal pc 0 code2+len)} := by
      simpa only [holEl_eq_getElem j newShmemInfo hj,getMemopInfo] using hrecord
    simp only [List.getElem_map]
    conv_lhs => rw [hr]
    cases addr with
    | addr base off => simp [BitVec.ofNat_add,getMemopInfo]
  · intro pc line ⟨hf,hn⟩ x hx ⟨a,hxa,ha⟩
    subst x
    have hnot := hexclude a line pc hf ha
    have hdropMem : mc.target.getPc ms + BitVec.ofNat width a + BitVec.ofNat width (posVal pc 0 code2)
        ∈ mc.ffiEntryPcs.drop i := by
      have hx' := hx
      rw [←List.take_append_drop i mc.ffiEntryPcs] at hx'
      exact (List.mem_append.mp hx').resolve_left hnot
    have hnatMem : (mc.target.getPc ms + BitVec.ofNat width a + BitVec.ofNat width (posVal pc 0 code2)).toNat
        ∈ newShmemInfo.map ShmemInfoNum.entryPc := by
      rw [hentries,←List.map_drop]
      exact List.mem_map.mpr ⟨_,hdropMem,rfl⟩
    have hlo : (mc.target.getPc ms).toNat ≤
        (mc.target.getPc ms + BitVec.ofNat width a + BitVec.ofNat width (posVal pc 0 code2)).toNat := by
      rw [hoff,List.map_map] at hnatMem
      obtain ⟨rec,_,hr⟩ := List.mem_map.mp hnatMem
      dsimp only [Function.comp_def] at hr
      omega
    have hnext := asmFetchAux_posVal_successor pc 0 code2 0 mc.target.config labs
      (mc.ffiNames.take i) line ⟨henc,hf⟩
    have hb := posVal_bound (pc+1) 0 code2 mc.target.config labs (mc.ffiNames.take i) 0 henc
    have hsmall : a+posVal pc 0 code2 < 2^width := by omega
    have hnoWrap : (mc.target.getPc ms).toNat+(a+posVal pc 0 code2) < 2^width :=
      initializer_wordAdd_noWrap _ _ hsmall (by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hlo)
    have hnat : (mc.target.getPc ms + BitVec.ofNat width a + BitVec.ofNat width (posVal pc 0 code2)).toNat =
        (mc.target.getPc ms).toNat+a+posVal pc 0 code2 := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,BitVec.toNat_add,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hsmall,Nat.mod_eq_of_lt hnoWrap]
      omega
    have hdis := hok.2 pc line ⟨hf,hn⟩
    exact Set.disjoint_left.mp hdis hnatMem ⟨a,ha,hnat⟩
end Flapjack.Compiler.Backend.LabToTarget

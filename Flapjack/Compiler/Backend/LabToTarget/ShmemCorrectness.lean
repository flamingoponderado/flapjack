import Mathlib.Data.Set.Lattice
import Flapjack.Compiler.Backend.LabToTarget.ShmemMembership
import Flapjack.Compiler.Backend.LabToTarget.ByteIntervalDistinct
import Flapjack.Compiler.Backend.LabToTarget.MmioShmem
import Flapjack.Compiler.Backend.LabToTarget.ShmemDistinct
import Flapjack.Misc.FindIndex.Distinct
import Flapjack.Compiler.Backend.LabToTarget.FetchValidity
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Basis.Pure.MlString

private instance : Nonempty HolFfiName := ⟨.sharedMem .mappedRead⟩
private instance : Nonempty ShmemInfoNum := ⟨⟨0,0,0,0,0,0⟩⟩

/-- Flapjack bounded paired-list infrastructure. An actual ZIP member yields
its shared index and a successful search of the record projection. Every EL
is reduced under a bound supplied by that membership, without any default. -/
theorem pairedEntry_findIndex {α β : Type} [Nonempty α] [Nonempty β]
    (names : List α) (records : List β) (key : β → Nat) (name : α) (record : β)
    (hm : (name,record) ∈ List.zip names records)
    (hn : (records.map key).Nodup) :
    ∃ index, index < names.length ∧ index < records.length ∧
      Flapjack.Misc.findIndex (key record) (records.map key) 0 = some index ∧
      holEl index names = name ∧ holEl index records = record := by
  obtain ⟨index,hbound,hpair⟩ := List.mem_iff_getElem.mp hm
  have hnBound : index < names.length := by
    simp only [List.length_zip] at hbound
    omega
  have hrBound : index < records.length := by
    simp only [List.length_zip] at hbound
    omega
  have hname : names[index]'hnBound = name := by
    simpa only [List.getElem_zip] using congrArg Prod.fst hpair
  have hrecord : records[index]'hrBound = record := by
    simpa only [List.getElem_zip] using congrArg Prod.snd hpair
  refine ⟨index,hnBound,hrBound,?_,?_,?_⟩
  · apply (Flapjack.Misc.findIndex_allDistinct_elEq (records.map key) hn
      (key record) 0 index).mpr
    refine ⟨index,by omega,by simpa using hrBound,?_⟩
    rw [holEl_eq_getElem index _ (by simpa using hrBound),List.getElem_map,hrecord]
  · exact (holEl_eq_getElem index names hnBound).trans hname
  · exact (holEl_eq_getElem index records hrBound).trans hrecord

/-- Flapjack infrastructure for the second conjunct of the full source theorem.
Each extracted record comes from an actual shared-memory fetch at its own PC;
there is no independent named HOL declaration for this inversion. -/
theorem shmemInfo_entryOrigin {width : Nat} [NeZero width]
    (code : LabProgHOL width) (p validPos : Nat) (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName) (record : ShmemInfoNum)
    (he : allEncOk c labs ffis validPos code)
    (hm : record ∈ (getShmemInfo code p [] []).2) :
    ∃ pc op reg addr bytes len,
      asmFetchAux pc code = some (.asm (.shareMem op reg addr) bytes len) ∧
      record.entryPc = posVal pc p code := by
  rw [getShmemInfo_characterization code p [] [] validPos c labs ffis he] at hm
  simp only [List.unzip_eq_map,List.nil_append,List.mem_map] at hm
  obtain ⟨pair,hpair,rfl⟩ := hm
  obtain ⟨entries,hentries,hpair⟩ := List.mem_flatten.mp hpair
  simp only [List.map_map,Function.comp_def,List.mem_map] at hentries
  obtain ⟨pc,_hpc,rfl⟩ := hentries
  cases hf : asmFetchAux pc code with
  | none => simp [lineToInfo,hf] at hpair
  | some line =>
    cases line with
    | label a b n => simp [lineToInfo,hf] at hpair
    | labAsm a w bytes len => simp [lineToInfo,hf] at hpair
    | asm inst bytes len =>
      cases inst with
      | asmi inst => simp [lineToInfo,hf] at hpair
      | cbw a b => simp [lineToInfo,hf] at hpair
      | shareMem op reg addr =>
        cases addr with
        | addr base off =>
          rcases hmem : getMemopInfo op with ⟨name,nb⟩
          simp only [lineToInfo,hf,hmem,List.mem_singleton] at hpair
          subst pair
          exact ⟨pc,op,reg,.addr base off,bytes,len,hf,rfl⟩

/-- Flapjack assembly infrastructure for the actual shared-memory fetch.
The witness uses extracted paired membership, not an assumed search result. -/
theorem shmemInfo_sharedIndex {width : Nat} [NeZero width]
    (code : LabProgHOL width) (p validPos : Nat) (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (he : allEncOk c labs ffis validPos code) (hc : encOk c)
    (hsize : (progToBytes code).length < 2^width)
    (pc : Nat) (op : HolMemop) (reg : Nat) (addr : HolAddr width)
    (bytes : List (BitVec 8)) (len : Nat)
    (hf : asmFetchAux pc code = some (.asm (.shareMem op reg addr) bytes len)) :
    ∃ index, index < (getShmemInfo code p [] []).1.length ∧
      index < (getShmemInfo code p [] []).2.length ∧
      Flapjack.Misc.findIndex (p+posVal pc 0 code)
        ((getShmemInfo code p [] []).2.map ShmemInfoNum.entryPc) 0 = some index ∧
      holEl index (getShmemInfo code p [] []).1 = .sharedMem (getMemopInfo op).1 ∧
      holEl index (getShmemInfo code p [] []).2 =
        {entryPc:=p+posVal pc 0 code,nbytes:=(getMemopInfo op).2,
         addrReg:=match addr with | .addr base _ => base,
         addrOff:=match addr with | .addr _ off => off.toNat,
         reg:=reg,exitPc:=p+(posVal pc 0 code+len)} := by
  rcases hmem : getMemopInfo op with ⟨name,nb⟩
  have hm := getShmemInfo_mem c labs ffis validPos code pc op reg addr bytes len name nb p
    ⟨he,hf,hmem⟩
  have hn := getShmemInfo_entryDistinct code c labs ffis validPos p ⟨hsize,hc,he⟩
  obtain ⟨index,hb1,hb2,hsearch,hname,hrecord⟩ :=
    pairedEntry_findIndex _ _ ShmemInfoNum.entryPc _ _ hm hn
  have hvalid := allEncOk_fetch_lineOk c labs ffis pc validPos code _ ⟨he,hf⟩
  have hlen : bytes.length = len := by
    simp only [lineOk] at hvalid
    exact hvalid.2.1
  have hpos := posVal_accZero pc p code
  have hexit := posVal_accZero pc (p+bytes.length) code
  refine ⟨index,hb1,hb2,?_,?_,?_⟩
  · rw [←hpos] at hsearch
    exact hsearch
  · simpa only [hmem] using hname
  · rw [←hpos,←hexit] at hrecord
    simpa only [hmem,hlen,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hrecord

/-- Flapjack assembly infrastructure proving the entire non-shared-memory
byte-interval separation result from the original encoding and size guards.
This remains untagged until the full original conjunction is assembled. -/
theorem shmemInfo_nonSharedDisjoint {width : Nat} [NeZero width]
    (code : LabProgHOL width) (p validPos : Nat) (c : AsmConfigExact width)
    (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (he : allEncOk c labs ffis validPos code) (hc : encOk c)
    (hsize : (progToBytes code).length < 2^width)
    (pc : Nat) (line : LabLineHOL width)
    (hf : asmFetchAux pc code = some line)
    (hn : ∀ op reg addr bytes len, line ≠ .asm (.shareMem op reg addr) bytes len) :
    Disjoint ({n | n ∈ ((getShmemInfo code p [] []).2.map ShmemInfoNum.entryPc)} : Set Nat)
      {n | ∃ a, a < (lineBytes line).length ∧ n = p+a+posVal pc 0 code} := by
  apply Set.disjoint_left.mpr
  intro n hentry hbyte
  obtain ⟨record,hm,rfl⟩ := List.mem_map.mp hentry
  obtain ⟨other,op,reg,addr,bytes,len,hother,hpos⟩ :=
    shmemInfo_entryOrigin code p validPos c labs ffis record he hm
  obtain ⟨a,ha,heq⟩ := hbyte
  have hne : other ≠ pc := by
    intro h
    subst other
    have hline : line = .asm (.shareMem op reg addr) bytes len :=
      Option.some.inj (hf.symm.trans hother)
    exact hn op reg addr bytes len hline
  have hdistinct := posVal_asmFetchAux_distinct c labs ffis validPos code
    pc line a other p ⟨he,hc,hf,ha,hsize,hne⟩
  have hzero := posVal_accZero pc p code
  rw [hpos] at heq
  apply hdistinct
  omega
/-- Full original shared-memory extraction correctness. Every source guard and
both quantified conclusion families remain, with arbitrary FFI prefixes and
independent query/validity starts. All EL uses are proved bounded; no total
default, assumed search result, target execution or extra bound is used. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem getShmemInfo_ok {width : Nat} [NeZero width]
    (c : AsmConfigExact width) (labs : Spt (Spt Nat)) (validFfis : List HolFfiName)
    (validPos : Nat)
    (code : List (Section (Line (AsmOrCbw (HolAsm width) HolMemop (HolAddr width))
      (AsmWithLab HolCmp (HolRegImm width) MlString) (BitVec width))))
    (ffis : List HolFfiName) (p : Nat)
    (newFfiNames : List HolFfiName) (newShmemInfo : List ShmemInfoNum) :
    allEncOk c labs validFfis validPos code ∧ encOk c ∧
      (progToBytes code).length < 2^width ∧
      (∀ x ∈ ffis, ∃ name, x = HolFfiName.extCall name) ∧
      getShmemInfo code p ffis [] = (newFfiNames,newShmemInfo) →
    (∀ pc op reg addr bytes len i,
      asmFetchAux pc code = some (.asm (.shareMem op reg addr) bytes len) ∧
        mmioPcsMinIndex newFfiNames = some i →
      ∃ index, Flapjack.Misc.findIndex (p+posVal pc 0 code)
          (newShmemInfo.map ShmemInfoNum.entryPc) 0 = some index ∧
        (let (name,nb) := getMemopInfo op
         holEl (index+i) newFfiNames = .sharedMem name ∧
         holEl index newShmemInfo =
           {entryPc:=(holEl index newShmemInfo).entryPc,nbytes:=nb,
            addrReg:=match addr with | .addr base _ => base,
            addrOff:=match addr with | .addr _ off => off.toNat,
            reg:=reg,exitPc:=p+(posVal pc 0 code+len)})) ∧
    (∀ pc line, asmFetchAux pc code = some line ∧
      (∀ op reg addr bytes len, line ≠ .asm (.shareMem op reg addr) bytes len) →
      Disjoint ({n | n ∈ newShmemInfo.map ShmemInfoNum.entryPc} : Set Nat)
        {n | ∃ a, a < (lineBytes line).length ∧ n = p+a+posVal pc 0 code}) := by
  rintro ⟨he,hc,hsize,hffis,hout⟩
  have hprefix := getShmemInfo_prepend code p ffis [] newFfiNames newShmemInfo hout
  have hnames := hprefix.1
  have hrecords : newShmemInfo = (getShmemInfo code p [] []).2 := by
    simpa only [List.nil_append] using hprefix.2
  have hmmio := mmioPcsMinIndex_getShmemInfo c labs validFfis validPos code
    ffis p newFfiNames newShmemInfo ⟨he,hc,hffis,hout⟩
  constructor
  · intro pc op reg addr bytes len i ⟨hf,hi⟩
    have hindex : i = ffis.length := Option.some.inj (hi.symm.trans hmmio)
    subst i
    obtain ⟨index,hbn,hbr,hsearch,hname,hrecord⟩ :=
      shmemInfo_sharedIndex code p validPos c labs validFfis he hc hsize
        pc op reg addr bytes len hf
    refine ⟨index,by simpa only [hrecords] using hsearch,?_⟩
    dsimp only
    constructor
    · rw [hnames]
      have hb : index+ffis.length < (ffis++(getShmemInfo code p [] []).1).length := by
        simp only [List.length_append]; omega
      rw [holEl_eq_getElem _ _ hb,List.getElem_append_right (by omega)]
      have hsub : index+ffis.length-ffis.length = index := by omega
      simp only [hsub]
      exact (holEl_eq_getElem index _ hbn).symm.trans hname
    · rw [hrecords]
      have hentry := congrArg ShmemInfoNum.entryPc hrecord
      rw [hrecord]
  · intro pc line ⟨hf,hn⟩
    rw [hrecords]
    exact shmemInfo_nonSharedDisjoint code p validPos c labs validFfis he hc hsize
      pc line hf hn
end Flapjack.Compiler.Backend.LabToTarget

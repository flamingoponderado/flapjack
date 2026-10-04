import Flapjack.Compiler.Backend.LabToTarget.FilterSkipSafety
import Flapjack.Compiler.Backend.LabToTarget.ImplementsIntro
import Flapjack.Compiler.Backend.LabToTarget.Initialization.Semantics
import Flapjack.Compiler.Backend.LabToTarget.FilterSkip
import Flapjack.Compiler.Backend.LabToTarget.SkipFilterPreconditions
import Flapjack.Compiler.Backend.LabToTarget.FindFfiNamesEvery
import Flapjack.Compiler.Backend.LabToTarget.ListSubset
import Flapjack.Compiler.Backend.LabToTarget.MmioShmem
import Flapjack.Compiler.Backend.LabFilter.Proofs.SectionEnd
import Flapjack.Compiler.Backend.LabFilter.Map

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabProps.LabelSets
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.LabToTarget.FilterSkip

/-- Flapjack infrastructure assembling the seven original code conjuncts
from their reviewed filtering laws. No separate HOL theorem names this
intermediate consequence of good_code_def. The label value type stays generic. -/
private theorem goodCodeFiltered {width : Nat} [NeZero width] {G : Type}
    (config : AsmConfigExact width) (labels : Spt (Spt G)) (code : LabProgHOL width) :
    goodCode config labels code → goodCode config labels (filterSkip code) := by
  rintro ⟨hend, hsec, hdistinct, hlabels, hdisjoint, htargets, hpre⟩
  refine ⟨Flapjack.Compiler.Backend.LabFilter.Proofs.secEndsWithLabelFilterSkip code hend,
    ?_, ?_, ?_, ?_, ?_, allEncOkPreFilterSkip code config hpre⟩
  · intro sectionData hmem line hline
    rw [filterSkipMap] at hmem
    obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hmem
    exact hsec original horiginal line (List.mem_filter.mp hline).1
  · simpa only [mapSectionNumFilterSkip] using hdistinct
  · intro sectionData hmem
    have hlabelsMem : extractLabels sectionData.lines ∈
        (filterSkip code).map (fun sectionData => extractLabels sectionData.lines) :=
      List.mem_map.mpr ⟨sectionData,hmem,rfl⟩
    rw [filterSkipExtractLabels] at hlabelsMem
    obtain ⟨original,horiginal,heq⟩ := List.mem_map.mp hlabelsMem
    rw [← heq]
    exact hlabels original horiginal
  · simpa only [mapSectionNumFilterSkip] using hdisjoint
  · simpa only [getLabelsFilterSkip,getCodeLabelsFilterSkip] using htargets

/-- Flapjack infrastructure exposing the actual bounded list entry returned
by the native search recursion. It is not a port of HOL's total EL/LEAST law;
no out-of-range choice is used and no distinctness premise is introduced. -/
private theorem successfulIndex {α : Type} [DecidableEq α] (values : List α)
    (target : α) (offset index : Nat) (h : findIndex target values offset = some index) :
    ∃ i, ∃ hi : i < values.length, index = offset+i ∧ values[i]'hi = target := by
  induction values generalizing offset with
  | nil => simp [findIndex] at h
  | cons head tail ih =>
    by_cases he : head = target
    · have hs : offset = index := by simpa only [findIndex,if_pos he,Option.some.injEq] using h
      exact ⟨0,by simp,by omega,he⟩
    · have ht : findIndex target tail (offset+1) = some index := by
        simpa only [findIndex,if_neg he] using h
      obtain ⟨i,hi,hindex,hvalue⟩ := ih (offset+1) ht
      exact ⟨i+1,by simp; omega,by omega,by simpa using hvalue⟩

/-- Flapjack proof infrastructure for the numerical final buffer clause in
semantics_compile_lemma-prime's proof. There is no separately named HOL
lemma: it follows from the original start-PC contract, its MMIO boundary,
and its strict whole-buffer bound. Every search/list access stays in range. -/
private theorem bufferNotFfi {width : Nat} [NeZero width] {S Q : Type}
    (mc : MachineConfig width S Q) (pc : BitVec width) (size space i : Nat)
    (hstart : startPcOk mc pc) (hboundary : mmioPcsMinIndex mc.ffiNames = some i)
    (hbound : space+size+ffiOffset*(i+3) < 2^width) :
    ∀ bn, bn < space → BitVec.ofNat width bn + BitVec.ofNat width size + pc ∉
      mc.ffiEntryPcs.take i := by
  obtain ⟨_,_,_,_,_,_,_,boundary,hindex,hprefix,_,_⟩ := hstart
  have hi : boundary = i := Option.some.inj (hindex.symm.trans hboundary)
  subst boundary
  intro bn hbn hmem
  obtain ⟨j,hj,hvalue⟩ := List.mem_take_iff_getElem.mp hmem
  have hji : j < i := by omega
  have hfind := (hprefix j hji).2.2.2.2
  obtain ⟨found,hfound,hreturned,hentry⟩ := successfulIndex mc.ffiEntryPcs
    (pc - BitVec.ofNat width ((3+j)*ffiOffset)) 0 j hfind
  have hfj : found = j := by omega
  subst found
  have he : BitVec.ofNat width bn + BitVec.ofNat width size + pc =
      pc - BitVec.ofNat width ((3+j)*ffiOffset) := hvalue.symm.trans hentry
  have hs : (BitVec.ofNat width bn + BitVec.ofNat width size +
      BitVec.ofNat width ((3+j)*ffiOffset)) + pc = pc := by
    calc
      _ = (BitVec.ofNat width bn + BitVec.ofNat width size + pc) +
          BitVec.ofNat width ((3+j)*ffiOffset) := by ac_rfl
      _ = (pc - BitVec.ofNat width ((3+j)*ffiOffset)) +
          BitVec.ofNat width ((3+j)*ffiOffset) := congrArg (fun x => x + _) he
      _ = pc := BitVec.sub_add_cancel _ _
  have hz := congrArg (fun x => x-pc) hs
  simp only [BitVec.add_sub_cancel,BitVec.sub_self] at hz
  have hzNat := congrArg BitVec.toNat hz
  have hlt : bn+size+(3+j)*ffiOffset < 2^width := by
    simp only [ffiOffset] at hbound ⊢
    omega
  rw [← BitVec.ofNat_add,← BitVec.ofNat_add,BitVec.toNat_ofNat] at hzNat
  simp only [BitVec.toNat_zero,Nat.mod_eq_of_lt hlt] at hzNat
  simp only [ffiOffset] at hzNat
  omega

/-- Full original prime compiler-semantics lemma. All sixteen original guards
and the independently generic empty-label value type are retained. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem semanticsCompileLemmaPrime {width : Nat} [NeZero width] {S Q G : Type} {F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (ms : S)
    (code : LabProgHOL width) (asmConf : AsmConfigExact width) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → Config × LabProgHOL width) :
    mcConfOk mc ∧
    (noShareMemInst code → compilerOracleOk coracle cNext.labels bytes.length asmConf mc.ffiNames) ∧
    goodCode mc.target.config (.ln : Spt (Spt G)) code ∧
    asmConf = mc.target.config ∧ c.labels = .ln ∧ c.pos = 0 ∧
    compile asmConf c code = some (bytes,cNext) ∧ cNext.ffiNames = some mc.ffiNames ∧
    goodInitState mc ms bytes cbspace t m dm sdm ∧
    cNext.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
      (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
    mc.mmioInfo = List.zip ((List.range cNext.shmemExtra.length).map (fun index => index+i))
      (cNext.shmemExtra.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff), rec.reg,
        BitVec.ofNat width rec.exitPc + mc.target.getPc ms))) ∧
    noInstallOrNoShareMem code mc.ffiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
    cbspace+bytes.length+ffiOffset*(i+3) < 2^width ∧
    (∀ ffis, c.ffiNames = some ffis → ∀ name ∈ ffis, ∃ s, name = .extCall s) ∧
    semantics (makeInit mc ffi t m dm sdm ms code (compile asmConf)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle) ≠ .fail →
    machineSemHOL mc ffi ms = fun behavior => behavior =
      semantics (makeInit mc ffi t m dm sdm ms code (compile asmConf)
        (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle) := by
  rintro ⟨hmc,horacle,hgood,rfl,hlabs,hpos,hcompile,hffi,hinit,hentries,hmmio,
    hsafe,hboundary,hbound,hprovided,hnonfail⟩
  have hfilter := makeInitFilterSkip mc ffi t m dm sdm ms code
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle
  change semantics (makeInit mc ffi t m dm sdm ms (filterSkip code) (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
      (fun n => ((coracle n).1,filterSkip (coracle n).2))) =
    semantics (makeInit mc ffi t m dm sdm ms code (compile mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle) at hfilter
  rw [← hfilter] at hnonfail ⊢
  have hcomp := hcompile
  simp only [compile,compileLab,hlabs,hpos] at hcomp
  generalize hchoice : (match c.ffiNames with
    | some names => (names,listSubset (findFfiNames (filterSkip code)) names)
    | none => (findFfiNames (filterSkip code),true)) = choice at hcomp
  rcases choice with ⟨ffis,ffisOk⟩
  let finish (names : List HolFfiName) (ok : Bool) :=
    if ok then
      match removeLabels c.initClock mc.target.config 0 .ln names (filterSkip code) with
      | none => none
      | some (output,labs) =>
          let (newNames,info) := getShmemInfo output 0 [] []
          some (progToBytes output,{c with
            labels := labs
            pos := (progToBytes output).length+0
            secPosLen := getSymbols 0 output
            ffiNames := some (names++newNames)
            shmemExtra := info})
    else none
  have hfinished : finish ffis ffisOk = some (bytes,cNext) := by
    cases hcfg : c.ffiNames with
    | none =>
      simp only [hcfg,Prod.mk.injEq] at hchoice
      rw [← hchoice.1,← hchoice.2]
      cases hr : removeLabels c.initClock mc.target.config 0 .ln
          (findFfiNames (filterSkip code)) (filterSkip code) <;>
        simpa only [finish,hcfg,hr] using hcomp
    | some supplied =>
      simp only [hcfg,Prod.mk.injEq] at hchoice
      rw [← hchoice.1,← hchoice.2]
      cases hr : removeLabels c.initClock mc.target.config 0 .ln supplied (filterSkip code) <;>
        simpa only [finish,hcfg,hr] using hcomp
  clear hcomp
  have hcomp := hfinished
  dsimp only [finish] at hcomp
  by_cases hok : ffisOk = true
  · simp only [hok,↓reduceIte] at hcomp
    cases hremove : removeLabels c.initClock mc.target.config 0 .ln ffis (filterSkip code) with
    | none => simp only [hremove,reduceCtorEq] at hcomp
    | some output =>
      rcases output with ⟨code2,labs⟩
      simp only [hremove] at hcomp
      cases hinfo : getShmemInfo code2 0 [] [] with
      | mk newNames info =>
        simp only [hinfo,Option.some.injEq,Prod.mk.injEq] at hcomp
        obtain ⟨rfl,rfl⟩ := hcomp
        have hnames : mc.ffiNames = ffis++newNames := by
          simpa only [Option.some.injEq] using hffi.symm
        have hffis : ∀ name ∈ ffis, ∃ s, name = HolFfiName.extCall s := by
          cases hcfg : c.ffiNames with
          | none =>
            simp only [hcfg,Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact findFfiNamesEvery (filterSkip code) _ rfl
          | some supplied =>
            simp only [hcfg,Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact hprovided supplied hcfg
        have hnew : ∀ name ∈ newNames, ∀ s, name ≠ HolFfiName.extCall s := by
          obtain ⟨suffix,heq,hshared⟩ := getShmemInfo_mappedNames code2 0 [] [] newNames info hinfo
          simp only [List.nil_append] at heq
          rw [heq]
          intro name hmem s
          obtain ⟨op,rfl⟩ := hshared name hmem
          intro heq
          cases heq
        have hb : mmioPcsMinIndex mc.ffiNames = some ffis.length := by
          rw [hnames]
          exact mmioPcsMinIndex_append newNames ffis ⟨hnew,hffis⟩
        have hilen : i = ffis.length := Option.some.inj (hboundary.symm.trans hb)
        have htake : mc.ffiNames.take i = ffis := by
          rw [hnames,hilen,List.take_append_length]
        have hdrop : mc.ffiNames.drop i = newNames := by
          rw [hnames,hilen,List.drop_append_length]
        have hsubset : listSubset (findFfiNames (filterSkip code)) ffis = true := by
          cases hcfg : c.ffiNames with
          | none =>
            simp only [hcfg,Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact listSubsetRefl _
          | some supplied =>
            simp only [hcfg,Prod.mk.injEq] at hchoice
            rw [← hchoice.1]
            exact hchoice.2.trans hok
        let shiftedInfo := info.map (fun rec => { rec with
          entryPc := (mc.target.getPc ms).toNat+rec.entryPc,
          exitPc := (mc.target.getPc ms).toNat+rec.exitPc })
        apply semanticsMakeInit (G := G) mc ms ffi (filterSkip code) code2 labs c.initClock i
          cbspace t m dm sdm (fun n => ((coracle n).1,filterSkip (coracle n).2))
          newNames info shiftedInfo
        refine ⟨hmc.2.1,goodCodeFiltered _ _ _ hgood,hmc,?_,?_,?_,hinit,hinfo,rfl,hdrop,
          hboundary,?_,?_,?_,?_,hnonfail⟩
        · intro hno
          obtain ⟨hall,hzero⟩ := horacle ((noShareMemFilterSkip code).mp hno)
          refine ⟨?_,hzero⟩
          intro k
          exact ⟨goodCodeFiltered _ _ _ (hall k).1,
            (noShareMemFilterSkip (coracle k).2).mpr (hall k).2⟩
        · rw [htake]
          simp only [listSubset,List.all_eq_true,decide_eq_true_eq] at hsubset ⊢
          intro name hmem
          exact hsubset name (List.mem_filter.mp hmem).1
        · simpa only [htake] using hremove
        · simpa only [shiftedInfo,List.map_map,Function.comp_def] using hentries
        · simpa only [shiftedInfo,List.length_map,List.map_map,Function.comp_def,
            BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,BitVec.add_comm] using hmmio
        · exact noInstallOrNoShareMemFilterSkip code mc.ffiNames hsafe
        · have hstart : startPcOk mc (mc.target.getPc ms) := by
            rw [← hinit.2.2.1]
            exact hinit.2.2.2.1
          exact bufferNotFfi mc _ _ cbspace i hstart hboundary hbound
  · simp only [hok,↓reduceIte,reduceCtorEq] at hcomp

/-- Full original precise implementation refinement, derived from the prime
semantics equality with its non-Fail guard discharged inside implements. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem semanticsCompileLemma {width : Nat} [NeZero width] {S Q G : Type} {F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (ms : S)
    (code : LabProgHOL width) (asmConf : AsmConfigExact width) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → Config × LabProgHOL width) :
    mcConfOk mc ∧
    (noShareMemInst code → compilerOracleOk coracle cNext.labels bytes.length asmConf mc.ffiNames) ∧
    goodCode mc.target.config (.ln : Spt (Spt G)) code ∧
    asmConf = mc.target.config ∧ c.labels = .ln ∧ c.pos = 0 ∧
    compile asmConf c code = some (bytes,cNext) ∧ cNext.ffiNames = some mc.ffiNames ∧
    goodInitState mc ms bytes cbspace t m dm sdm ∧
    cNext.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
      (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
    mc.mmioInfo = List.zip ((List.range cNext.shmemExtra.length).map (fun index => index+i))
      (cNext.shmemExtra.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff), rec.reg,
        BitVec.ofNat width rec.exitPc + mc.target.getPc ms))) ∧
    noInstallOrNoShareMem code mc.ffiNames ∧ mmioPcsMinIndex mc.ffiNames = some i ∧
    cbspace+bytes.length+ffiOffset*(i+3) < 2^width ∧
    (∀ ffis, c.ffiNames = some ffis → ∀ name ∈ ffis, ∃ s, name = .extCall s) →
    Flapjack.SemanticsPropsHOL.implementsPrimeHOL true (machineSemHOL mc ffi ms)
      (fun behavior => behavior = semantics (makeInit mc ffi t m dm sdm ms code (compile asmConf)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle)) := by
  rintro ⟨hmc,horacle,hgood,hasm,hlabs,hpos,hcompile,hffi,hinit,hentries,hmmio,
    hsafe,hboundary,hbound,hprovided⟩
  apply implementsIntroGen true
  · rintro ⟨_,hnonfail⟩
    exact semanticsCompileLemmaPrime (G := G) mc ffi ms code asmConf c cNext bytes cbspace i
      t m dm sdm coracle ⟨hmc,horacle,hgood,hasm,hlabs,hpos,hcompile,hffi,hinit,hentries,hmmio,
        hsafe,hboundary,hbound,hprovided,hnonfail⟩
  · rfl

end Flapjack.Compiler.Backend.LabToTarget

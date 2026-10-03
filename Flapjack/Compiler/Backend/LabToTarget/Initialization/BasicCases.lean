import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.Compiler.Backend.LabToTarget.StateRel
import Flapjack.Compiler.Backend.LabToTarget.RemoveLabelsCorrectness
import Flapjack.Compiler.Backend.LabToTarget.CodeSimilar.CodeSafety
import Flapjack.Compiler.Backend.LabToTarget.ByteLengths
import Flapjack.Compiler.Backend.Semantics.TargetSem.InitializationContracts
import Flapjack.Compiler.Backend.Semantics.TargetProps.PostInterferenceState
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Encoders.Asm Flapjack.Misc

/-- Flapjack word-addition infrastructure for the literal source buffer address;
there is no independently named HOL declaration being ported. -/
private theorem initializer_wordAdd_left_comm {width : Nat} (a b c : BitVec width) :
    a + (b+c) = b+(a+c) := by
  rw [←BitVec.add_assoc,BitVec.add_comm a b,BitVec.add_assoc]

/-- Ten genuine cases of the complete original initializer theorem: ISR4
(oracle), ISR5 (labels), ISR6 (FFI names), ISR7 (bytes), ISR9 (memory), ISR10
(buffer space), ISR11 (empty buffer), ISR13 (initial PC), ISR14 (sections),
and ISR17 (safety). Every original binder and all fourteen guards remain.
The conclusion is precisely these conjuncts of stateRel applied to the actual
makeInit state. This case group does not establish ISR1/2/3/8/12/15/16 or the
assembling theorem. No output execution or post-state invariant is assumed. -/
@[hol "cakeml/compiler/backend/proofs/lab_to_targetProofScript.sml"
  "IMP_state_rel_make_init" (words_as_type_indexed_bitvec)]
theorem makeInit_stateRel_basicCases {width : Nat} [NeZero width] {S Q : Type} {F : Type}
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
    (noShareMemInst code2 → ∀ k,
      let (cfg, program) := initial.compileOracle k
      goodCode mc.target.config cfg.labels program ∧ noShareMemInst program ∧
      (k = 0 → cfg.labels = labs ∧ cfg.pos = (progToBytes code2).length ∧
        cfg.ffiNames = some mc.ffiNames)) ∧
    (∀ sid lid value, labLookup sid lid labs = some value → value % 2 = 0) ∧
    listSubset ((findFfiNames initial.code).filter (fun x => match x with
      | .extCall _ => true | _ => false)) mc.ffiNames = true ∧
    (progToBytes code2).length % 2 = 0 ∧
    (∀ a, initial.memDomain (holByteAlign a) = true →
      t.memDomain a ∧ initial.memDomain a = true ∧
      wordLocValByte (mc.target.getPc ms) labs initial.memory a initial.be = some (t.mem a)) ∧
    (∀ n, n < initial.codeBuffer.spaceLeft →
      let address := initial.codeBuffer.position + BitVec.ofNat width (initial.codeBuffer.buffer.length+n)
      t.memDomain address ∧ ¬ initial.memDomain address = true) ∧
    bytesInMemHOL initial.codeBuffer.position initial.codeBuffer.buffer t.mem t.memDomain
      (fun a => initial.memDomain a = true) ∧
    t.pc = mc.target.getPc ms + BitVec.ofNat width (posVal initial.pc 0 code2) ∧
    (∀ sec ∈ code2, secLabelsOk sec) ∧ noInstallOrNoShareMem code2 mc.ffiNames := by
  rintro ⟨hgood,hmc,horacle,hffis,hremove,hinit,hinfo,hoff,hdrop,hboundary,hentries,hmmio,hsafe,hbuffer⟩
  obtain ⟨hends,hlabels,hids,hdistinct,hdis,hsub,hpre⟩ := hgood
  have hr := removeLabels_correct clock mc.target.config 0 .ln (mc.ffiNames.take i) code code2 labs
  have hresult := hr ⟨hremove,hmc.2.2.2.2.2.2.2,hends,hlabels,hids,hdistinct,hdis,hsub,hpre,by decide,
    by simp [labLookup, sptLookup]⟩
  obtain ⟨henc,hsim,hodd,heven,hpreserve,hlookup⟩ := hresult
  have hcodeSafety := codeSimilar_noInstallOrNoShareMem code code2 mc.ffiNames ⟨hsim,hsafe⟩
  have hor : noShareMemInst code2 → ∀ k,
      let (cfg, program) := coracle k
      goodCode mc.target.config cfg.labels program ∧ noShareMemInst program ∧
      (k = 0 → cfg.labels = labs ∧ cfg.pos = (progToBytes code2).length ∧
        cfg.ffiNames = some mc.ffiNames) := by
    intro hs k
    have hh := horacle (codeSimilar_noShareMem code2 code ⟨codeSimilar_sym code code2 hsim,hs⟩)
    obtain ⟨ha,hb⟩ := hh
    dsimp only [compilerOracleOk] at ha hb
    have ha' := ha k
    refine ⟨ha'.1,ha'.2,?_⟩
    intro hk
    subst k
    exact hb
  obtain ⟨hrel,hconfigured,hpc,hstart,halign,hinter,hffi,hcache,hloaded,hbytes,hdom,hclosed,hshared,
    hshClosed,hdisjoint,hword,hspace,hsize⟩ := hinit
  obtain ⟨hfailed,hbe,hta,htdomain,hlr⟩ := hconfigured
  obtain ⟨hdim,hencoder,hptr,hlen,hptr2,hlen2,hlink,hencc⟩ := hmc
  have hevenBytes := allEncOk_progToBytes_even code2 mc.target.config labs (mc.ffiNames.take i) 0
    ⟨by decide,henc⟩
  have hsections := codeSimilar_secLabelsOk code code2 ⟨hlabels,hsim⟩
  have hzero := posVal_zero code2 mc.target.config labs (mc.ffiNames.take i) 0 henc
  have hmemory : ∀ a, dm (holByteAlign a) = true →
      t.memDomain a ∧ dm a = true ∧
      wordLocValByte (mc.target.getPc ms) labs m a mc.target.config.bigEndian = some (t.mem a) := by
    intro a ha
    obtain ⟨w,hbyte,hmem⟩ := hword a
    refine ⟨hdom a (hclosed a ha),hclosed a ha,?_⟩
    rw [wordLocValByte_word _ _ _ _ _ _ hmem,hbyte]
  have hbufferSpace : ∀ n, n < cbspace →
      t.memDomain (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length + BitVec.ofNat width n) ∧
      ¬ dm (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length + BitVec.ofNat width n) = true := by
    intro n hn
    simpa only [hpc,BitVec.ofNat_add,BitVec.add_assoc,BitVec.add_comm,initializer_wordAdd_left_comm] using hspace n hn
  have hnames : listSubset ((findFfiNames code).filter (fun x => match x with
      | .extCall _ => true | _ => false)) mc.ffiNames = true := by
    simp only [listSubset,List.all_eq_true,decide_eq_true_eq] at hffis ⊢
    intro name hn
    exact List.mem_of_mem_take (hffis name hn)
  dsimp only [makeInit]
  refine ⟨hor,heven,hnames,hevenBytes,hmemory,by simpa only [List.length_nil,Nat.zero_add] using hbufferSpace,by trivial,?_,hsections,hcodeSafety⟩
  simpa [hzero] using hpc

end Flapjack.Compiler.Backend.LabToTarget

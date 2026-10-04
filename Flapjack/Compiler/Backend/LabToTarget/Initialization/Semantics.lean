import Flapjack.Compiler.Backend.LabFilter.Proofs.Semantics
import Flapjack.Compiler.Backend.LabToTarget.MachineSemantics
namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabProps Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps Flapjack.Misc

/-- Flapjack infrastructure for the vacuous source value type of the literal
empty label tree. Both domains are empty and every remaining goodCode conjunct
is identical. It has no separate HOL original and permits every original G. -/
private theorem emptyGoodCode {width : Nat} [NeZero width] {G H : Type}
    (c : AsmConfigExact width) (code : LabProgHOL width) :
    goodCode c (.ln : Spt (Spt G)) code ↔ goodCode c (.ln : Spt (Spt H)) code := by
  have hd : Set.ofPred (sptDomain (.ln : Spt (Spt G))) =
      Set.ofPred (sptDomain (.ln : Spt (Spt H))) := by
    ext key
    simp [sptDomain, sptLookup]
  simp only [goodCode, labsDomain_ln, hd]

/-- Original full initializer semantics theorem, with all sixteen source
guards and the independent empty-label value type G retained. The actual
initializer supplies the full initOk witnesses through the checked seventeen
state-relation cases and unconditional oracle tie; full machineSemEqSem then
derives the exact behavior singleton. Existing evaluator real-rendering
assurance is inherited (SOUNDNESS item8). -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem semanticsMakeInit {width : Nat} [NeZero width] {S Q G : Type} {F : Type}
    (mc : MachineConfig width S Q) (ms : S) (ffi : HolFfiState F)
    (code code2 : LabProgHOL width) (labs : Spt (Spt Nat))
    (clock i cbspace : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → Config × LabProgHOL width)
    (newFfiNames : List HolFfiName) (shmemInfo newShmemInfo : List ShmemInfoNum) :
    encoderCorrect mc.target ∧ goodCode mc.target.config (.ln : Spt (Spt G)) code ∧ mcConfOk mc ∧
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
      mc.target.getPc ms ∉ mc.ffiEntryPcs.take i) ∧
    semantics (makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle) ≠ .fail →
    machineSemHOL mc ffi ms = fun behavior => behavior =
      semantics (makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
        (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle) := by
  rintro ⟨hencoder, hgood, hrest⟩
  have hgoodNat : goodCode mc.target.config (.ln : Spt (Spt Nat)) code :=
    (emptyGoodCode (G := G) (H := Nat) mc.target.config code).mp hgood
  obtain ⟨hmc, horacle, hffis, hremove, hinit, hinfo, hoff, hdrop, hboundary,
    hentries, hmmio, hsafe, hbuffer, hnonfail⟩ := hrest
  have hentry := makeInit_initOk mc ms ffi code code2 labs clock i cbspace t m dm sdm
    coracle newFfiNames shmemInfo newShmemInfo
    ⟨hgoodNat, hmc, horacle, hffis, hremove, hinit, hinfo, hoff, hdrop, hboundary,
      hentries, hmmio, hsafe, hbuffer⟩
  exact machineSemEqSem mc (mc.target.getPc ms) ms
    (makeInit mc ffi t m dm sdm ms code (compileLab mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width (progToBytes code2).length) cbspace coracle)
    ⟨hencoder, hentry, hnonfail⟩

/-- Full original skip-filter initialization semantics equality. The actual
compileLab and complete memory, domain, machine, buffer and oracle arguments
are retained; both initial states discharge the original filter guards. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem makeInitFilterSkip {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (ms : S) (code : LabProgHOL width) (cbpos : BitVec width) (cbspace : Nat)
    (coracle : Nat → Config × LabProgHOL width) :
    semantics (makeInit mc ffi t m dm sdm ms (Flapjack.Compiler.Backend.LabFilter.filterSkip code)
      (compileLab mc.target.config) cbpos cbspace
      (fun n => ((coracle n).1, Flapjack.Compiler.Backend.LabFilter.filterSkip (coracle n).2))) =
    semantics (makeInit mc ffi t m dm sdm ms code
      (fun configuration program => compileLab mc.target.config configuration
        (Flapjack.Compiler.Backend.LabFilter.filterSkip program)) cbpos cbspace coracle) := by
  apply Flapjack.Compiler.Backend.LabFilter.Proofs.filterSkipSemantics
  exact ⟨rfl, rfl, ⟨compileLab mc.target.config, rfl, rfl⟩, rfl⟩

end Flapjack.Compiler.Backend.LabToTarget

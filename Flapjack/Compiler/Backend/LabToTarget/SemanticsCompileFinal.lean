import Flapjack.Compiler.Backend.LabToTarget.SemanticsCompile
import Flapjack.Compiler.Backend.LabProps.DomainAlignmentDmEvaluate
import Flapjack.Compiler.Backend.LabProps.DomainAlignmentSdmEvaluate

namespace Flapjack.Compiler.Backend.LabToTarget
open Flapjack Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm Flapjack.Misc Flapjack.SemanticsPropsHOL

/-- Full final Lab-to-target refinement with both original byte-aligned domains.
The target machine, projection and FFI host remain independent. The proof
inherits the native evaluator's rational-cuts assumption (SOUNDNESS item 8).
This pass theorem does not establish the still-open whole compiler composition. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem semanticsCompile {width : Nat} [NeZero width] {S Q : Type} {F : Type}
    (mc : MachineConfig width S Q) (ffi : HolFfiState F) (ms : S)
    (code : LabProgHOL width) (asmConf : AsmConfigExact width) (c cNext : Config)
    (bytes : List (BitVec 8)) (cbspace i : Nat) (t : AsmState width)
    (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (coracle : Nat → Config × LabProgHOL width) :
    mcConfOk mc ∧
    (noShareMemInst code → compilerOracleOk coracle cNext.labels bytes.length asmConf mc.ffiNames) ∧
    goodCode asmConf c.labels code ∧
    asmConf = mc.target.config ∧ c.labels = .ln ∧ c.pos = 0 ∧
    compile asmConf c code = some (bytes,cNext) ∧ cNext.ffiNames = some mc.ffiNames ∧
    goodInitState mc ms bytes cbspace t m dm sdm ∧
    mmioPcsMinIndex mc.ffiNames = some i ∧
    cNext.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
      (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
    mc.mmioInfo = List.zip ((List.range cNext.shmemExtra.length).map (fun index => index+i))
      (cNext.shmemExtra.map (fun rec => (rec.nbytes,
        HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff), rec.reg,
        BitVec.ofNat width rec.exitPc + mc.target.getPc ms))) ∧
    noInstallOrNoShareMem code mc.ffiNames ∧
    cbspace+bytes.length+ffiOffset*(i+3) < 2^width ∧
    (∀ ffis, c.ffiNames = some ffis → ∀ name ∈ ffis, ∃ s, name = .extCall s) →
    Flapjack.SemanticsPropsHOL.implementsPrimeHOL true (machineSemHOL mc ffi ms)
      (fun behavior => behavior = semantics (makeInit mc ffi t m (fun a => dm a && holByteAligned a)
        (fun a => sdm a && holByteAligned a) ms code (compile asmConf)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle)) := by
  rintro ⟨hmc,horacle,hgood,hasm,hlabs,hpos,hcompile,hffi,hinit,hboundary,
    hentries,hmmio,hsafe,hbound,hprovided⟩
  let initial := makeInit mc ffi t m dm sdm ms code (compile asmConf)
    (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle
  let sharedAligned := makeInit mc ffi t m dm (fun a => sdm a && holByteAligned a)
    ms code (compile asmConf) (mc.target.getPc ms + BitVec.ofNat width bytes.length)
    cbspace coracle
  have hbase : implementsPrimeHOL true (machineSemHOL mc ffi ms)
      (fun behavior => behavior = semantics initial) := by
    apply semanticsCompileLemma (G := Nat) mc ffi ms code asmConf c cNext bytes cbspace i
      t m dm sdm coracle
    refine ⟨hmc,horacle,?_,hasm,hlabs,hpos,hcompile,hffi,hinit,hentries,hmmio,
      hsafe,hboundary,hbound,hprovided⟩
    simpa only [hasm,hlabs] using hgood
  have hshared : implementsPrimeHOL true
      (fun behavior => behavior = semantics initial)
      (fun behavior => behavior = semantics sharedAligned) := by
    change implementsPrimeHOL true (fun behavior => behavior = semantics initial)
      (fun behavior => behavior = semantics (alignSdm initial))
    exact implementsAlignSDM initial hmc.1
  apply implementsPrimeTransHOL _ (fun behavior => behavior = semantics sharedAligned) _ true
  constructor
  · change implementsPrimeHOL true (fun behavior => behavior = semantics sharedAligned)
      (fun behavior => behavior = semantics (alignDm sharedAligned))
    exact implementsAlignDM sharedAligned hmc.1
  · exact implementsPrimeTransHOL _ _ _ true ⟨hshared,hbase⟩

end Flapjack.Compiler.Backend.LabToTarget

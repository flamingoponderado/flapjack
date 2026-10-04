import Flapjack.Pancake.Proofs.PanToTarget.AssemblyLabToTarget
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyGoodCode
import Flapjack.Compiler.Backend.LabToTarget.SemanticsCompileFinal

/-!
# `pan_to_target_compile_semantics` assembly, stage A4

The application of `lab_to_targetProof$semantics_compile` in the HOL proof of
`pan_to_target_compile_semantics` (`pan_to_targetProofScript.sml:1316-1440`): the
machine semantics implements the lab semantics of the initial lab state
`labst = make_init mc ffi t m (dm ∩ byte_aligned) (sdm ∩ byte_aligned) ms lprog
(compile mc.target.config) ...` with the constant oracle of the HOL proof. An
intermediate step of the single HOL proof, so untagged.

Its premises are the `compile_prog_max` results, the configuration hypotheses,
`pan_installed`'s components and, for `good_code` (stage A2), the conclusion of
`pan_to_word_every_inst_ok_less` (`hinst`). `hinst` is a stage-local premise: the
top theorem discharges it from `pancake_good_code` once
`pan_to_word_every_inst_ok_less` (bead .14.20) is ported; it is not a premise of
the top theorem.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Pancake.PanLang

/-- Stage A4 of the HOL proof (lines 1316-1440): `semantics_compile` for the initial
lab state, with `no_install_or_no_share_mem` (A1), `compiler_oracle_ok` (A1),
`good_code` (A2), `compile_lab_IMP_mmio_pcs_min_index` and `pan_installed`'s
`good_init_state`, MMIO and code-buffer facts. -/
theorem panToTargetMachineLab {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState σ)
    (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapsDm sdm : BitVec width → Bool) (ms : S) (bytes : List (BitVec 8)) (cbspace : Nat)
    (panCode : List (DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (wconf : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (ltconf : LabToTarget.Config)
    (hcfg : BackendProof.backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, wconf, fs, p))
    (hlab : LabToTarget.compile mc.target.config c.labConf
      (StackToLab.compile c.stackConf c.dataConf (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
        (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
        mc.target.config.addrOffset p) = some (bytes, ltconf))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hffiOk : match c.labConf.ffiNames with
      | none => True
      | some l => ∀ x ∈ l, ∃ s, x = HolFfiName.extCall s)
    -- `pan_installed`'s components
    (hgi : goodInitState mc ms bytes cbspace t m
      (fun w => decide (t.regs (StackNames.findNameSpt c.stackConf.regNames 2) ≤ w ∧
        w < t.regs (StackNames.findNameSpt c.stackConf.regNames 4)) || bitmapsDm w) sdm)
    (hffi : ltconf.ffiNames = some mc.ffiNames)
    (hmmio : ∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      ltconf.shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range ltconf.shmemExtra.length).map (fun index => index + i))
          (ltconf.shmemExtra.map fun rec => (rec.nbytes,
            HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff),
            rec.reg, BitVec.ofNat width rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + ffiOffset * (i + 3) < 2 ^ width)
    -- stage-local: the conclusion of `pan_to_word_every_inst_ok_less` (bead .14.20)
    (hinst : ∀ q ∈ panToWordCompileProgHOL mc.target.config.isa panCode,
      everyInst (fun i => instOkLessExact mc.target.config (HolInst.ofWordLangInst i)) q.2.2 =
        true) :
    let regNames := c.stackConf.regNames
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let maxHeap := 2 * DataToWord.maxHeapLimit width c.dataConf - 1
    let labst := LabToTarget.makeInit (C := LabToTarget.Config) mc ffi t m
      (fun a => (heapStackDm a || bitmapsDm a) && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms
      (StackToLab.compile c.stackConf c.dataConf maxHeap sp mc.target.config.addrOffset p)
      (LabToTarget.compile mc.target.config)
      (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace
      (fun _ => (ltconf, StackToLab.compileNoStubs regNames c.stackConf.jump
        mc.target.config.addrOffset sp []))
    SemanticsPropsHOL.implementsPrimeHOL true (machineSemHOL mc ffi ms)
      (fun b => b = LabSem.semantics labst) := by
  intro regNames r1 r2 heapStackDm sp maxHeap labst
  have hpos : c.labConf.pos = 0 := hcfg.2.2.2.2.1
  have hlabels : c.labConf.labels = .ln := hcfg.2.2.2.2.2.1
  have hgc := panToTargetGoodCode (β := Nat) c mc panCode col wprog bitmaps wconf fs p hcfg hmc.1
    hisa hwtw hwts hnodup hinst
  obtain ⟨ffis, hffis, i, hi⟩ := BackendProof.compileLabIMPMmioPcsMinIndex mc.target.config
    c.labConf _ bytes ltconf ⟨hlab, hffiOk⟩
  rw [hffi] at hffis
  cases hffis
  obtain ⟨hshm, hmmioI, hbound⟩ := hmmio i hi
  have horacle := panToTargetCompilerOracleOk mc.target.config c.labConf ltconf _ bytes
    mc.ffiNames regNames c.stackConf.jump mc.target.config.addrOffset sp hlab hpos hffi
  have hnis := panToTargetNoInstallOrNoShareMem panCode mc.target.config mc.target.config.isa _
    c.wordToWordConf col wprog bitmaps wconf fs p c.stackConf c.dataConf maxHeap sp
    mc.target.config.addrOffset mc.ffiNames ⟨hnodup, hisa, rfl, hwtw, hwts⟩
  exact semanticsCompile mc ffi ms _ mc.target.config c.labConf ltconf bytes cbspace i t m
    (fun w => heapStackDm w || bitmapsDm w) sdm _
    ⟨hmc, fun _ => horacle, by rw [hlabels]; exact hgc, rfl, hlabels, hpos, hlab, hffi, hgi, hi,
      hshm, hmmioI, hnis, hbound, fun ffis h => by rw [h] at hffiOk; exact hffiOk⟩

end Flapjack.Pancake.Proofs.PanToTarget

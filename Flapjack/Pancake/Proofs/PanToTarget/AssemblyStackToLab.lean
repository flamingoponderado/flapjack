import Flapjack.Pancake.Proofs.PanToTarget.LabelsChain
import Flapjack.Compiler.Backend.BackendProof.ConfigOk
import Flapjack.Compiler.Backend.BackendProof.MachineInit
import Flapjack.Compiler.Backend.LabToTarget.Initialization
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.Compiler.Backend.Semantics.TargetProps.CalleeSaved
import Flapjack.Compiler.Backend.StackToLab.Proofs.GoodCode

/-!
# `pan_to_target_compile_semantics` assembly, stage A3a

The facts about the initial lab state `labst = make_init mc ffi t m (dm ∩ byte_aligned)
(sdm ∩ byte_aligned) ms code ...` that the HOL proof of
`pan_to_target_compile_semantics` (`pan_to_targetProofScript.sml:1460-1484`) establishes
before applying `stack_to_labProof$full_make_init_semantics`: callee-saved and oracle
register facts, word-aligned memory domains, `good_code` of the stack program and of
the (empty) oracle programs, the register-name facts and `¬failed`. HOL's
`set mc.callee_saved_regs` is the Bool predicate `fun k => decide (k ∈ ...)` used as
`full_make_init`'s `save_regs`. An intermediate step of the single HOL proof, not a
HOL theorem, so untagged; all premises are hypotheses of the top theorem.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.Semantics.TargetProps Flapjack.Pancake.PanLang

/-- Stage A3a of the HOL proof (lines 1460-1484). -/
theorem panToTargetLabstFacts {width : Nat} [NeZero width] {S Q F C : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (ffi : HolFfiState F)
    (t : AsmState width) (m : BitVec width → WordLocW width) (dm sdm : BitVec width → Bool)
    (ms : S) (code : LabSem.LabProgHOL width)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (cbpos : BitVec width) (cbspace : Nat) (coracle : Nat → C × LabSem.LabProgHOL width)
    (panCode : List (DeclHOL width)) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bitmaps : List (BitVec width))
    (c'' : WordToStack.Native.Config) (fs : List Nat) (p : List (Nat × StackLang.HolProg width))
    (hcfg : backendConfigOk mc.target.config c) (hmc : mcConfOk mc)
    (hinit : mcInitOk mc.target.config c mc) (hisa : mc.target.config.isa ≠ .ag32)
    (hwtw : WordToWord.compile c.wordToWordConf mc.target.config
      (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog))
    (hwts : WordToStack.Native.compileNative mc.target.config false wprog =
      (bitmaps, c'', fs, p))
    (hnodup : ((functionsHOL panCode).map Prod.fst).Nodup) :
    let labst := makeInit (C := C) mc ffi t m (fun a => dm a && holByteAligned a)
      (fun a => sdm a && holByteAligned a) ms code comp cbpos cbspace coracle
    let sp := mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3)
    let saveRegs := fun k => decide (k ∈ mc.calleeSavedRegs)
    ¬ saveRegs labst.linkReg = true ∧ labst.pc = 0 ∧
    (∀ k i n, saveRegs k = true → labst.ioRegs n i k = none) ∧
    (∀ k n, saveRegs k = true → labst.ccRegs n k = none) ∧
    (∀ x : BitVec width, labst.memDomain x = true → x.toNat % (width / 8) = 0) ∧
    (∀ x : BitVec width, labst.sharedMemDomain x = true → x.toNat % (width / 8) = 0) ∧
    StackToLab.Proofs.GoodCode.goodCode sp p ∧
    StackToLab.Proofs.GoodCode.goodCode sp ([] : List (Nat × StackLang.HolProg width)) ∧
    10 ≤ sp ∧
    (∀ r ∈ [2, 3, 4],
      saveRegs (StackNames.findNameSpt c.stackConf.regNames (r + sp - 2)) = true) ∧
    StackNames.findNameSpt c.stackConf.regNames 4 = labst.len2Reg ∧
    StackNames.findNameSpt c.stackConf.regNames 3 = labst.ptr2Reg ∧
    StackNames.findNameSpt c.stackConf.regNames 2 = labst.lenReg ∧
    StackNames.findNameSpt c.stackConf.regNames 1 = labst.ptrReg ∧
    StackNames.findNameSpt c.stackConf.regNames 0 = labst.linkReg ∧
    Function.Bijective (StackNames.findNameSpt c.stackConf.regNames) ∧
    ¬ labst.failed = true := by
  intro labst sp saveRegs
  obtain ⟨hcallee, h4, h3, h2, h1, h0, -, -, -, -, -, hlinkCallee, -⟩ := hinit
  have hgood : goodDimindex width := hmc.1
  have hregs : mc.target.config.avoidRegs.length + 13 ≤ mc.target.config.regCount :=
    hcfg.2.2.2.1
  have hbij := hcfg.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbij, by simp [labst, makeInit]⟩
  · simp only [saveRegs, labst, makeInit, decide_eq_true_eq]
    cases hl : mc.target.config.linkReg <;> simp_all
  · intro k i n hk
    exact targetIoRegsCalleeSaved mc ffi ms n k i (by simpa [saveRegs] using hk)
  · intro k n hk
    exact targetCcRegsCalleeSaved mc ffi ms n k (by simpa [saveRegs] using hk)
  · intro x hx
    simp only [labst, makeInit, Bool.and_eq_true] at hx
    exact byteAlignedMOD hgood x hx.2
  · intro x hx
    simp only [labst, makeInit, Bool.and_eq_true] at hx
    exact byteAlignedMOD hgood x hx.2
  · exact word_to_stack_good_code_lemma c mc panCode col wprog bitmaps c'' fs p
      ⟨hwtw, hisa, hwts, hregs, hnodup⟩
  · simp [StackToLab.Proofs.GoodCode.goodCode]
  · simp only [sp]; omega
  · intro r hr
    have := hcallee r hr
    have heq : r + sp - 2 =
        r + mc.target.config.regCount - (mc.target.config.avoidRegs.length + 5) := by
      simp only [sp]; omega
    simpa [saveRegs, heq] using this
  · exact h4
  · exact h3
  · exact h2
  · exact h1
  · simp only [labst, makeInit]
    cases hl : mc.target.config.linkReg <;> simp_all

end Flapjack.Pancake.Proofs.PanToTarget

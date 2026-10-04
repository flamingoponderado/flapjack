import Flapjack.Pancake.Proofs.PanToTarget.LabelsChain
import Flapjack.Pancake.Proofs.PanToTarget.CompileProgMax
import Flapjack.Compiler.Backend.BackendProof.CompileLab
import Flapjack.Compiler.Backend.LabToTarget.CodeSafety
import Flapjack.Compiler.Backend.LabToTarget.GoodCode
import Flapjack.Compiler.Backend.LabToTarget.InitializationContracts
import Flapjack.Compiler.Backend.StackToLab.Compile

/-!
# `pan_to_target_compile_semantics` assembly, stage A1

The `no_install_or_no_share_mem` and `compiler_oracle_ok` facts that the HOL proof
of `pan_to_target_compile_semantics` (`pan_to_targetProofScript.sml:1331-1370`)
derives for the lab program produced by `compile_prog_max`, before applying
`lab_to_targetProof$semantics_compile`. These are intermediate steps of that single
HOL proof, not separate HOL theorems, so they carry no `@[hol]` tag; each is
stated over hypotheses that the top theorem itself provides.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Pancake.PanLang

/-- The lab program of the Pancake pipeline is `no_install`, hence
`no_install_or_no_share_mem` for any FFI-name list (HOL proof lines 1331-1338,
via the reviewed `from_pan_to_lab_no_install`). -/
theorem panToTargetNoInstallOrNoShareMem {width : Nat} [NeZero width]
    (panCode : List (DeclHOL width)) (ac : AsmConfigExact width) (isa : AsmArchitecture)
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (wc : WordToWord.Config) (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width))) (bm : List (BitVec width))
    (wconf : WordToStack.Native.Config) (fs : List Nat)
    (p : List (Nat × StackLang.HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (lim regc : Nat)
    (off : BitVec width × BitVec width) (ffis : List HolFfiName)
    (h : ((functionsHOL panCode).map Prod.fst).Nodup ∧ ac.isa ≠ .ag32 ∧
      panToWordCompileProgHOL isa panCode = wprog0 ∧
      WordToWord.compile wc ac wprog0 = (col, wprog) ∧
      WordToStack.Native.compileNative ac false wprog = (bm, wconf, fs, p)) :
    noInstallOrNoShareMem (StackToLab.compile scc dc lim regc off p) ffis :=
  Or.inr (from_pan_to_lab_no_install panCode ac isa wprog0 wc col wprog bm wconf fs p
    scc dc lim regc off h)

/-- `compiler_oracle_ok` for the constant oracle of the HOL proof (lines 1340-1368):
every oracle entry is the final lab configuration with the empty
`compile_no_stubs` program. -/
theorem panToTargetCompilerOracleOk {width : Nat} [NeZero width]
    (ac : AsmConfigExact width) (lc ltconf : LabToTarget.Config)
    (lprog : LabSem.LabProgHOL width) (bytes : List (BitVec 8)) (ffis : List HolFfiName)
    (regNames : Spt Nat) (jump : Bool) (off : BitVec width × BitVec width) (sp : Nat)
    (hcompile : LabToTarget.compile ac lc lprog = some (bytes, ltconf))
    (hpos : lc.pos = 0) (hffi : ltconf.ffiNames = some ffis) :
    compilerOracleOk (fun _ => (ltconf, StackToLab.compileNoStubs regNames jump off sp []))
      ltconf.labels bytes.length ac ffis := by
  have hlen := BackendProof.compileLabLENGTH ac lc _ bytes ltconf hcompile
  rw [hpos, Nat.add_zero] at hlen
  refine ⟨fun _ => ?_, ⟨rfl, hlen, hffi⟩⟩
  simp only [StackToLab.compileNoStubs, List.map_nil]
  simp [StackNames.compileHOL, goodCode, LabProps.noShareMemInst,
    LabProps.LabelSets.getLabels, BackendProps.restrictNonzero, LabProps.allEncOkPreHOL,
    LabSem.asmFetchAux]

/-- Unfolding a successful `compile_prog_max` through `from_stack`, `from_lab` and
`attach_bitmaps` (the opening of the HOL proof, lines 1300-1314): the word-to-word,
word-to-stack and lab-to-target results, the final configuration and the stack
bound. -/
theorem compileProgMax_some {width : Nat} [NeZero width] {S Q : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (panCode : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stackMax : Option Nat)
    (h : compileProgMax c mc panCode = (some (bytes, bitmaps, c'), stackMax)) :
    ∃ col wprog wconf fs p ltconf,
      WordToWord.compile c.wordToWordConf mc.target.config
        (panToWordCompileProgHOL mc.target.config.isa panCode) = (col, wprog) ∧
      WordToStack.Native.compileNative mc.target.config false wprog = (bitmaps, wconf, fs, p) ∧
      LabToTarget.compile mc.target.config c.labConf
        (StackToLab.compile c.stackConf c.dataConf
          (2 * DataToWord.maxHeapLimit width c.dataConf - 1)
          (mc.target.config.regCount - (mc.target.config.avoidRegs.length + 3))
          mc.target.config.addrOffset p) = some (bytes, ltconf) ∧
      c' = { c with
        labConf := ltconf
        symbols := ltconf.secPosLen.map fun (name, position, length) =>
          (lookupAny name (.ln : Spt Basis.Pure.MlString.MlString)
            (Basis.Pure.MlString.ofString "NOTFOUND"), position, length) } ∧
      stackMax = WordDepth.maxDepth wconf.stackFrameSize
        (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wprog)) := by
  unfold compileProgMax at h
  simp only at h
  generalize hw : WordToWord.compile c.wordToWordConf mc.target.config
    (panToWordCompileProgHOL mc.target.config.isa panCode) = w at h
  obtain ⟨col, wprog⟩ := w
  generalize hs : WordToStack.Native.compileNative mc.target.config false wprog = st at h
  obtain ⟨bm, wconf, fs, p⟩ := st
  simp only [Backend.fromStack, Backend.fromLab, Prod.mk.injEq] at h
  obtain ⟨hl, hmax⟩ := h
  generalize hlab : LabToTarget.compile mc.target.config c.labConf _ = out at hl
  rcases out with _ | ⟨bytes', ltconf⟩
  · simp [Backend.attachBitmaps] at hl
  · simp only [Backend.attachBitmaps, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl, rfl⟩ := hl
    exact ⟨col, wprog, wconf, fs, p, ltconf, rfl, hs, hlab, rfl, hmax.symm⟩

end Flapjack.Pancake.Proofs.PanToTarget

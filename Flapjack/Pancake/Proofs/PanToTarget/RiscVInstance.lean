import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTop
import Flapjack.Compiler.Backend.RiscVConfig.PancakeConfigOk

/-!
# `pan_to_target_compile_semantics` at RISC-V with Pancake's configuration

The tagged `panToTargetCompileSemantics` instantiated at the RISC-V target, with the backend
configuration Pancake actually compiles with: `pancake_backend_conf riscv_backend_config`
(`compilerScript.sml:744-747`, `gc_kind := None`) and a machine configuration satisfying
`is_riscv_machine_config`. The configuration premises `backend_config_ok`, `mc_conf_ok` and
`mc_init_ok` are discharged by `riscvPancakeBackendConfigOk`, the tagged
`riscv_machine_config_ok` and `riscvPancakeInitOk`; the ISA, FFI-name and configuration-only
heap-bound (`riscvPancakeHeapLimit_lt`) premises are decided
by the concrete configuration. Every other premise of the top theorem is kept unchanged.

Untagged: HOL has no Pancake RISC-V instantiation (its `riscv_compile_correct` instantiates
the CakeML `compile_correct` with `riscv_backend_config`). Through the RISC-V L3 model this
theorem inherits the reals_as_rational_cuts assurance limit (SOUNDNESS section 8). It is a
statement about the logical compiler `compile_prog_max`; it does not establish that the
executed `flapjack-compile` route computes that function.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target

/-- The top theorem's configuration-only heap bound `bytes_in_word * (2 * max_heap_limit
(:64) c.data_conf - 1) < dimword (:64)`, decided for Pancake's RISC-V configuration
(Flapjack-specific; no HOL original). -/
theorem riscvPancakeHeapLimit_lt :
    (wordSemBytesInWord : BitVec 64).toNat *
        (2 * DataToWord.maxHeapLimit 64
          (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig).dataConf - 1) < 2 ^ 64 := by
  simp only [DataToWord.maxHeapLimit, DataToWord.shiftLength, riscvBackendConfig,
    Flapjack.wordShiftAmount, wordSemBytesInWord]
  decide

/-- `pan_to_target_compile_semantics` for RISC-V with `pancake_backend_conf
riscv_backend_config` and `is_riscv_machine_config mc`: the configuration premises are
discharged and the remaining premises are exactly those of the top theorem
(Flapjack-specific instantiation; no HOL original). -/
theorem panToTargetCompileSemanticsRiscV {σ : Type}
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (pan_code : List (DeclHOL 64)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 64 σ)
    (ms : RiscV.L3.riscv_state) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 64)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isRiscvMachineConfig mc →
    compileProgMax (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig) mc pan_code =
      (some (bytes, bitmaps, c'), stack_max) ∧
    pancakeGoodCodeHOL pan_code = true ∧
    distinctParamsHOL (functionsHOL pan_code) ∧
    ((functionsHOL pan_code).map Prod.fst).Nodup ∧
    s.code = HolFiniteMapExact.empty ∧
    s.locals = HolFiniteMapExact.empty ∧
    s.globals = HolFiniteMapExact.empty ∧
    sizeOfEidsHOL pan_code < 2 ^ 64 ∧
    s.eshapes = HolFiniteMapExact.empty ∧
    (0 : BitVec 64) < mc.target.getReg ms mc.lenReg ∧
    globals_size =
      (let dec_shs := decShapesHOL pan_code
       let struct_ctxt := decsStcnamesHOLExact (width := 64) [] pan_code
       (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
    mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.lenReg = s.baseAddr ∧
    globalsAllocatableHOL s pan_code ∧
    heap_len = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (64 / 8) ∧
    s.topAddr = s.baseAddr + (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 heap_len -
      BitVec.ofNat 64 (globals_size * 64 / 8) ∧
    globals_size ≤ heap_len ∧
    s.memaddrs = StackRemove.addresses (mc.target.getReg ms mc.lenReg) (heap_len - globals_size) ∧
    holAligned (wordShiftAmount 64 + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true ∧
    adj_ptr2 = mc.target.getReg ms mc.lenReg +
      (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc ∧
    adj_ptr4 = mc.target.getReg ms mc.len2Reg -
      (wordSemBytesInWord : BitVec 64) * BitVec.ofNat 64 StackRemove.maxStackAlloc ∧
    adj_ptr2 ≤ mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.ptr2Reg ≤ adj_ptr4 ∧
    (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (wordSemBytesInWord : BitVec 64).toNat *
        (2 * DataToWord.maxHeapLimit 64
          (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig).dataConf - 1) ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig).stackConf.regNames)
      mc c'.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL mc ffi ms b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config
          (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig) mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start pan_code) b := by
  intro hmc ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hpos,
    hsize, hlt, hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4, hlo,
    hhi, hheap, hffi, hbe, hinst, hstart, hfail⟩
  have hconfig : mc.target.config = riscvConfig := by rw [hmc.1]; rfl
  have hcfg := riscvPancakeBackendConfigOk
  rw [← hconfig] at hcfg
  have hinit := riscvPancakeInitOk mc hmc
  rw [← hconfig] at hinit
  exact panToTargetCompileSemantics _ mc pan_code bytes bitmaps c' stack_max s ms globals_size
    heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start
    ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hcfg,
      riscvMachineConfigOk mc hmc, hinit, by rw [hconfig]; decide, hpos, hsize, hlt, hbase,
      halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4, hlo, hhi, hheap,
      riscvPancakeHeapLimit_lt, hffi, hbe, trivial, hinst, hstart, hfail⟩

end Flapjack.Pancake.Proofs.PanToTarget

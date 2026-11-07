import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTop
import Flapjack.Compiler.Backend.Arm8Config.BackendProof
import Flapjack.Compiler.Backend.Arm8Config.BackendProofL3
import Flapjack.Compiler.Backend.Arm8Config.ProofsL3

/-!
# `pan_to_target_compile_semantics` at the L3 ARMv8 target

The tagged `panToTargetCompileSemantics` instantiated at the L3 ARMv8 machine
model (`arm8_state`/`arm8_proj`) with Pancake's backend configuration.
`backend_config_ok`, `mc_conf_ok` and `mc_init_ok` are discharged from
`isArm8MachineConfigL3`; the encoder-correctness obligation is
`arm8EncoderCorrectL3` from `L3/CorrectnessEncoding/Complete.lean`.

This is a statement about the logical compiler `compile_prog_max`; it does not
establish that the executed `flapjack-compile` route computes that function.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.Arm8Config Flapjack.Compiler.Encoders.Arm8.L3
open Flapjack.Compiler.Encoders.Arm8.L3.Target

/-- The top theorem's configuration-only heap bound, decided for Pancake's ARMv8
configuration (Flapjack-specific; no HOL original).  `Arm8Instance.lean` proves
the same statement as `arm8PancakeHeapLimit_lt`; this module does not import it,
and Lean lets the two same-named declarations coexist silently (the later import
wins), so the L3 copy is renamed rather than left to shadow it. -/
theorem arm8PancakeHeapLimitL3_lt :
    (wordSemBytesInWord : BitVec 64).toNat *
        (2 * DataToWord.maxHeapLimit 64
          (Flapjack.Compiler.pancakeBackendConf arm8BackendConfig).dataConf - 1) < 2 ^ 64 := by
  simp only [DataToWord.maxHeapLimit, DataToWord.shiftLength, arm8BackendConfig,
    arm8BackendConfigWith, Flapjack.Compiler.pancakeBackendConf, Flapjack.wordShiftAmount,
    wordSemBytesInWord]
  decide

/-- `pan_to_target_compile_semantics` for L3 ARMv8 with `pancake_backend_conf
arm8_backend_config` and `is_arm8_machine_config mc`. -/
theorem panToTargetCompileSemanticsArm8L3 {σ : Type}
    (mc : MachineConfig 64 arm8_state Arm8L3Projection)
    (pan_code : List (DeclHOL 64)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 64 σ)
    (ms : arm8_state) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 64)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isArm8MachineConfigL3 mc →
    compileProgMax (Flapjack.Compiler.pancakeBackendConf arm8BackendConfig) mc pan_code =
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
          (Flapjack.Compiler.pancakeBackendConf arm8BackendConfig).dataConf - 1) ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs (Flapjack.Compiler.pancakeBackendConf arm8BackendConfig).stackConf.regNames)
      mc c'.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL mc ffi ms b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config
          (Flapjack.Compiler.pancakeBackendConf arm8BackendConfig) mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start pan_code) b := by
  intro hmc ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hpos,
    hsize, hlt, hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4, hlo,
    hhi, hheap, hffi, hbe, hinst, hstart, hfail⟩
  have hconfig : mc.target.config = arm8ConfigL3 := by rw [hmc.1]; rfl
  have hcfg := arm8BackendConfigOkL3
  rw [← hconfig] at hcfg
  have hinit := arm8InitOkL3_pancake mc hmc
  rw [← hconfig] at hinit
  exact panToTargetCompileSemantics _ mc pan_code bytes bitmaps c' stack_max s ms globals_size
    heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start
    ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hcfg,
      arm8MachineConfigOkL3 mc hmc, hinit, by rw [hconfig]; decide, hpos, hsize, hlt, hbase,
      halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4, hlo, hhi, hheap,
      arm8PancakeHeapLimitL3_lt, hffi, hbe, trivial, hinst, hstart, hfail⟩

end Flapjack.Pancake.Proofs.PanToTarget

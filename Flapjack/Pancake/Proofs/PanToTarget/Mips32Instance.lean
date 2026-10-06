import Flapjack.Pancake.Proofs.PanToTarget.AssemblyTop
import Flapjack.Compiler.Backend.Mips32Config.Proofs

/-!
# `pan_to_target_compile_semantics` at MIPS32 (Ziren) with Pancake's configuration

The tagged `panToTargetCompileSemantics` instantiated at the MIPS32 target over Ziren's ISA
model, with the configuration the MIPS32 driver compiles with:
`pancake_backend_conf mips32BackendConfig` and a machine configuration satisfying
`isMips32MachineConfig`. The configuration premises `backend_config_ok`, `mc_conf_ok` and
`mc_init_ok` are discharged by `mips32BackendConfigOk`, `mips32MachineConfigOk` (from
`mips32_encoder_correct`) and `mips32InitOk`; the ISA, FFI-name and configuration-only
heap-bound (`mips32PancakeHeapLimit_lt`) premises are decided by the concrete configuration.
Every other premise of the top theorem is kept unchanged.

Untagged: CakeML has no MIPS32 target. The machine semantics is Ziren's `ZirenDet.Isa`, so
the theorem's assurance ends at that model (`docs/SOUNDNESS.md`). It is a statement about
the logical compiler `compile_prog_max`; `Mips32InstanceExecutable` and
`Mips32NativeSourceCorrect` connect it to the executed compiler.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.Mips32Config Flapjack.Compiler.Encoders.Mips32

/-- The top theorem's configuration-only heap bound `bytes_in_word * (2 * max_heap_limit
(:32) c.data_conf - 1) < dimword (:32)`, decided for Pancake's MIPS32 configuration
(Flapjack-specific; no HOL original). -/
theorem mips32PancakeHeapLimit_lt :
    (wordSemBytesInWord : BitVec 32).toNat *
        (2 * DataToWord.maxHeapLimit 32
          (Flapjack.Compiler.pancakeBackendConf mips32BackendConfig).dataConf - 1) < 2 ^ 32 := by
  simp only [DataToWord.maxHeapLimit, DataToWord.shiftLength, mips32BackendConfig,
    mips32BackendConfigWith, Flapjack.Compiler.pancakeBackendConf, Flapjack.wordShiftAmount,
    wordSemBytesInWord]
  decide

/-- `backend_config_ok` holds of the GC-free configuration Pancake compiles with: no conjunct
of `backend_config_ok_def` reads `data_conf.gc_kind` (Flapjack-specific; no HOL original). -/
theorem mips32PancakeBackendConfigOk :
    backendConfigOk mips32Config (Flapjack.Compiler.pancakeBackendConf mips32BackendConfig) :=
  mips32BackendConfigOk

/-- `mc_init_ok` reads only the register names and endianness, which `pancake_backend_conf`
does not change (Flapjack-specific; no HOL original). -/
theorem mips32PancakeInitOk (mc : MachineConfig 32 ZirenDet.Isa.State Mips32Projection) :
    isMips32MachineConfig mc →
      mcInitOk mips32Config (Flapjack.Compiler.pancakeBackendConf mips32BackendConfig) mc :=
  mips32InitOk mc

/-- `pan_to_target_compile_semantics` for MIPS32 with `pancake_backend_conf
mips32BackendConfig` and `isMips32MachineConfig mc`: the configuration premises are
discharged and the remaining premises are exactly those of the top theorem
(Flapjack-specific instantiation; no HOL original). -/
theorem panToTargetCompileSemanticsMips32 {σ : Type}
    (mc : MachineConfig 32 ZirenDet.Isa.State Mips32Projection)
    (pan_code : List (DeclHOL 32)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 32))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 32 σ)
    (ms : ZirenDet.Isa.State) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 32)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isMips32MachineConfig mc →
    compileProgMax (Flapjack.Compiler.pancakeBackendConf mips32BackendConfig) mc pan_code =
      (some (bytes, bitmaps, c'), stack_max) ∧
    pancakeGoodCodeHOL pan_code = true ∧
    distinctParamsHOL (functionsHOL pan_code) ∧
    ((functionsHOL pan_code).map Prod.fst).Nodup ∧
    s.code = HolFiniteMapExact.empty ∧
    s.locals = HolFiniteMapExact.empty ∧
    s.globals = HolFiniteMapExact.empty ∧
    sizeOfEidsHOL pan_code < 2 ^ 32 ∧
    s.eshapes = HolFiniteMapExact.empty ∧
    (0 : BitVec 32) < mc.target.getReg ms mc.lenReg ∧
    globals_size =
      (let dec_shs := decShapesHOL pan_code
       let struct_ctxt := decsStcnamesHOLExact (width := 32) [] pan_code
       (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
    mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.lenReg = s.baseAddr ∧
    globalsAllocatableHOL s pan_code ∧
    heap_len = (mc.target.getReg ms mc.ptr2Reg + -1 * s.baseAddr).toNat / (32 / 8) ∧
    s.topAddr = s.baseAddr + (wordSemBytesInWord : BitVec 32) * BitVec.ofNat 32 heap_len -
      BitVec.ofNat 32 (globals_size * 32 / 8) ∧
    globals_size ≤ heap_len ∧
    s.memaddrs = StackRemove.addresses (mc.target.getReg ms mc.lenReg) (heap_len - globals_size) ∧
    holAligned (wordShiftAmount 32 + 1)
      (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg) = true ∧
    adj_ptr2 = mc.target.getReg ms mc.lenReg +
      (wordSemBytesInWord : BitVec 32) * BitVec.ofNat 32 StackRemove.maxStackAlloc ∧
    adj_ptr4 = mc.target.getReg ms mc.len2Reg -
      (wordSemBytesInWord : BitVec 32) * BitVec.ofNat 32 StackRemove.maxStackAlloc ∧
    adj_ptr2 ≤ mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.ptr2Reg ≤ adj_ptr4 ∧
    (mc.target.getReg ms mc.ptr2Reg + -1 * mc.target.getReg ms mc.lenReg).toNat ≤
      (wordSemBytesInWord : BitVec 32).toNat *
        (2 * DataToWord.maxHeapLimit 32
          (Flapjack.Compiler.pancakeBackendConf mips32BackendConfig).dataConf - 1) ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs (Flapjack.Compiler.pancakeBackendConf mips32BackendConfig).stackConf.regNames)
      mc c'.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL mc ffi ms b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config
          (Flapjack.Compiler.pancakeBackendConf mips32BackendConfig) mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start pan_code) b := by
  intro hmc ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hpos,
    hsize, hlt, hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4, hlo,
    hhi, hheap, hffi, hbe, hinst, hstart, hfail⟩
  have hconfig : mc.target.config = mips32Config := by rw [hmc.1]; rfl
  have hcfg := mips32PancakeBackendConfigOk
  rw [← hconfig] at hcfg
  have hinit := mips32PancakeInitOk mc hmc
  rw [← hconfig] at hinit
  exact panToTargetCompileSemantics _ mc pan_code bytes bitmaps c' stack_max s ms globals_size
    heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start
    ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hcfg,
      mips32MachineConfigOk mc hmc, hinit, by rw [hconfig]; decide, hpos, hsize, hlt, hbase,
      halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4, hlo, hhi, hheap,
      mips32PancakeHeapLimit_lt, hffi, hbe, trivial, hinst, hstart, hfail⟩

end Flapjack.Pancake.Proofs.PanToTarget

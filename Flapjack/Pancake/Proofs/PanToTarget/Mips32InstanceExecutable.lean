import Flapjack.Pancake.Proofs.PanToTarget.Mips32Instance
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMax

/-!
# The MIPS32 Pancake theorem against the callable compiler

`panToTargetCompileSemanticsMips32` restated with its compiler premise on the callable
`compileProgMaxExecutable` (proved equal to `compile_prog_max` by
`compileProgMaxExecutable_eq`), at Pancake's configuration
`pancake_backend_conf mips32BackendConfig`. A driver that runs this function obtains the
whole MIPS32 correctness conclusion from the remaining premises. Untagged Flapjack
corollary; HOL has no MIPS32 target. It does not establish that the
`flapjack-compile` CLI computes this function.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.Mips32Config Flapjack.Compiler.Encoders.Mips32

/-- `panToTargetCompileSemanticsMips32` with the callable `compileProgMaxExecutable` as the
compiler premise; every other premise and the conclusion are unchanged (Flapjack-specific
corollary; no HOL original). -/
theorem panToTargetCompileSemanticsMips32Executable {σ : Type}
    (mc : MachineConfig 32 ZirenDet.Isa.State Mips32Projection)
    (pan_code : List (DeclHOL 32)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 32))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 32 σ)
    (ms : ZirenDet.Isa.State) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 32)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isMips32MachineConfig mc →
    compileProgMaxExecutable (Flapjack.Compiler.pancakeBackendConf mips32BackendConfig) mc
      pan_code = (some (bytes, bitmaps, c'), stack_max) ∧
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
  intro hmc ⟨hcomp, rest⟩
  rw [compileProgMaxExecutable_eq] at hcomp
  exact panToTargetCompileSemanticsMips32 mc pan_code bytes bitmaps c' stack_max s ms
    globals_size heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start hmc ⟨hcomp, rest⟩

end Flapjack.Pancake.Proofs.PanToTarget

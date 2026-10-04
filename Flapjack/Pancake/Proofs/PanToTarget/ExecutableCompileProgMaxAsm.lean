import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMax
import Flapjack.Pancake.Proofs.PanToTarget.RiscVInstanceExecutable

/-! Assembler-only callable compiler interface.

`compileProgMaxExecutable` reads its machine configuration only through
`machine.target.config`. `compileProgMaxAsmExecutable` is the same computation taking that
assembler configuration directly, so a driver can compile without constructing a machine
configuration. The RISC-V correctness theorem is restated against it at Pancake's
configuration `pancake_backend_conf riscv_backend_config` and `riscv_config`. Flapjack
computation/interface infrastructure; no separately named HOL declaration. It does not
establish that the `flapjack-compile` CLI computes this function. -/

namespace Flapjack.Pancake.Proofs.PanToTarget
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target

/-- `compileProgMaxExecutable` with its machine configuration replaced by the assembler
configuration it reads: the native pan-to-word compiler, the executable word-to-word
composition, native word-to-stack, the original maximum-depth bound and `from_stack`.
Flapjack computation infrastructure. -/
def compileProgMaxAsmExecutable {width : Nat} [NeZero width]
    (config : Flapjack.Compiler.Backend.Backend.Config) (asmConf : AsmConfigExact width)
    (program : List (DeclHOL width)) :
    Option (List (BitVec 8) × List (BitVec width) ×
      Flapjack.Compiler.Backend.Backend.Config) × Option Nat :=
  let program := panToWordCompileProgHOL asmConf.isa program
  let (_coloring, wordProgram) :=
    WordToWord.compileExecutable config.wordToWordConf asmConf program
  let (bitmaps, wordConfig, _frames, stackProgram) :=
    WordToStack.Native.compileNative asmConf false wordProgram
  let maximum := WordDepth.maxDepth wordConfig.stackFrameSize
    (WordDepth.fullCallGraph BvlToBvi.initGlobalsLocation (sptFromAList wordProgram))
  (Flapjack.Compiler.Backend.Backend.fromStack asmConf config .ln stackProgram bitmaps,
    maximum)

/-- The callable compiler depends on the machine configuration only through its assembler
configuration (kernel definitional equality; Flapjack infrastructure). -/
theorem compileProgMaxExecutable_eq_asm {width : Nat} [NeZero width]
    {State Projection : Type} (config : Backend.Config)
    (machine : MachineConfig width State Projection) (program : List (DeclHOL width)) :
    compileProgMaxExecutable config machine program =
      compileProgMaxAsmExecutable config machine.target.config program := rfl

/-- The assembler-only callable compiler is `compile_prog_max` at every machine
configuration with that assembler configuration (Flapjack infrastructure). -/
theorem compileProgMaxAsmExecutable_eq {width : Nat} [NeZero width]
    {State Projection : Type} (config : Backend.Config)
    (machine : MachineConfig width State Projection) (program : List (DeclHOL width)) :
    compileProgMaxAsmExecutable config machine.target.config program =
      compileProgMax config machine program := by
  rw [← compileProgMaxExecutable_eq_asm, compileProgMaxExecutable_eq]

/-- The RISC-V Pancake correctness theorem with the compiler premise on the assembler-only
callable compiler at `pancake_backend_conf riscv_backend_config` and `riscv_config`; every
other premise and the conclusion are those of `panToTargetCompileSemanticsRiscV`
(Flapjack-specific corollary; no HOL original). -/
theorem panToTargetCompileSemanticsRiscVAsmExecutable {σ : Type}
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (pan_code : List (DeclHOL 64)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 64 σ)
    (ms : RiscV.L3.riscv_state) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 64)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isRiscvMachineConfig mc →
    compileProgMaxAsmExecutable (Flapjack.Compiler.pancakeBackendConf riscvBackendConfig)
      riscvConfig pan_code = (some (bytes, bitmaps, c'), stack_max) ∧
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
  intro hmc ⟨hcomp, rest⟩
  have hconfig : mc.target.config = riscvConfig := by rw [hmc.1]; rfl
  rw [← hconfig, ← compileProgMaxExecutable_eq_asm] at hcomp
  exact panToTargetCompileSemanticsRiscVExecutable mc pan_code bytes bitmaps c' stack_max s ms
    globals_size heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start hmc ⟨hcomp, rest⟩

end Flapjack.Pancake.Proofs.PanToTarget

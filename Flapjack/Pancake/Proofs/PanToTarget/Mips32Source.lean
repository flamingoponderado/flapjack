import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsm
import Flapjack.Pancake.Proofs.PanToTarget.Mips32InstanceExecutable
import Flapjack.Pancake.PanToTarget.MainFirstSemantics

/-!
# Source-level MIPS32 Pancake theorem for the CLI compiler call

The MIPS32 CLI compiles a parsed program by calling
`compileProgMaxAsmExecutable pancakeMips32BackendConfig mips32Config (mainFirstHOL decls)`.
This restates `panToTargetCompileSemanticsMips32AsmExecutable` for exactly that call. The
compiler-input premises remain on `mainFirstHOL decls`, which the compiler receives; the
semantic premise and the conclusion are about the original declarations `decls`, using
`semanticsDecls_mainFirstHOL` (which needs a `main` function: without one,
`mainFirstHOL` inserts a default `main` and the semantics differ). Untagged Flapjack
corollary; HOL has no MIPS32 target. It does not establish that the CLI performs
this call or how it obtains `decls` from source text.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.Mips32Config Flapjack.Compiler.Encoders.Mips32
open Flapjack.Pancake.PanToTarget (mainFirstHOL semanticsDecls_mainFirstHOL)

/-- The MIPS32 Pancake correctness theorem with the compiler premise on the assembler-only
callable compiler at `pancake_backend_conf mips32BackendConfig` and `mips32Config`; every
other premise and the conclusion are those of `panToTargetCompileSemanticsMips32`
(Flapjack-specific corollary; no HOL original). -/
theorem panToTargetCompileSemanticsMips32AsmExecutable {σ : Type}
    (mc : MachineConfig 32 ZirenDet.Isa.State Mips32Projection)
    (pan_code : List (DeclHOL 32)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 32))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 32 σ)
    (ms : ZirenDet.Isa.State) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 32)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isMips32MachineConfig mc →
    compileProgMaxAsmExecutable (Flapjack.Compiler.pancakeBackendConf mips32BackendConfig)
      mips32Config pan_code = (some (bytes, bitmaps, c'), stack_max) ∧
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
  have hconfig : mc.target.config = mips32Config := by rw [hmc.1]; rfl
  rw [← hconfig, ← compileProgMaxExecutable_eq_asm] at hcomp
  exact panToTargetCompileSemanticsMips32Executable mc pan_code bytes bitmaps c' stack_max s ms
    globals_size heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start hmc ⟨hcomp, rest⟩


/-- MIPS32 correctness for the CLI's compiler call on `mainFirstHOL decls`, stated against
the source semantics of the original declarations `decls`, which must contain a `main`
function (Flapjack-specific corollary; no HOL original). -/
theorem panToTargetCompileSemanticsMips32Source {σ : Type}
    (mc : MachineConfig 32 ZirenDet.Isa.State Mips32Projection)
    (decls : List (DeclHOL 32)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 32))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 32 σ)
    (ms : ZirenDet.Isa.State) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 32)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isMips32MachineConfig mc →
    (∃ fi : FunDeclHOL 32, .function fi ∈ decls ∧ fi.name = ofString "main") →
    compileProgMaxAsmExecutable pancakeMips32BackendConfig mips32Config (mainFirstHOL decls) =
      (some (bytes, bitmaps, c'), stack_max) ∧
    pancakeGoodCodeHOL (mainFirstHOL decls) = true ∧
    distinctParamsHOL (functionsHOL (mainFirstHOL decls)) ∧
    ((functionsHOL (mainFirstHOL decls)).map Prod.fst).Nodup ∧
    s.code = HolFiniteMapExact.empty ∧
    s.locals = HolFiniteMapExact.empty ∧
    s.globals = HolFiniteMapExact.empty ∧
    sizeOfEidsHOL (mainFirstHOL decls) < 2 ^ 32 ∧
    s.eshapes = HolFiniteMapExact.empty ∧
    (0 : BitVec 32) < mc.target.getReg ms mc.lenReg ∧
    globals_size =
      (let dec_shs := decShapesHOL (mainFirstHOL decls)
       let struct_ctxt := decsStcnamesHOLExact (width := 32) [] (mainFirstHOL decls)
       (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
    mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.lenReg = s.baseAddr ∧
    globalsAllocatableHOL s (mainFirstHOL decls) ∧
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
        (2 * DataToWord.maxHeapLimit 32 pancakeMips32BackendConfig.dataConf - 1) ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs pancakeMips32BackendConfig.stackConf.regNames)
      mc c'.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start decls ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL mc ffi ms b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config pancakeMips32BackendConfig mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start decls) b := by
  intro hmc hasMain ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes,
    hpos, hsize, hlt, hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4,
    hlo, hhi, hheap, hffi, hbe, hinst, hstart, hfail⟩
  have hsem := semanticsDecls_mainFirstHOL s start decls hasMain
  rw [← hsem] at hfail ⊢
  exact panToTargetCompileSemanticsMips32AsmExecutable mc (mainFirstHOL decls) bytes bitmaps c'
    stack_max s ms globals_size heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start hmc
    ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hpos, hsize, hlt,
      hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4, hlo, hhi, hheap,
      hffi, hbe, hinst, hstart, hfail⟩

end Flapjack.Pancake.Proofs.PanToTarget

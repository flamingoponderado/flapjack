module

public import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsm
public import Flapjack.Pancake.Proofs.PanToTarget.X64InstanceExecutable
public import Flapjack.Pancake.PanToTarget.MainFirstSemantics

@[expose] public section


/-!
# Source-level x86-64 Pancake theorem for the CLI compiler call

The x86-64 CLI compiles a parsed program by calling
`compileProgMaxAsmExecutable pancakeX64BackendConfig x64Config (mainFirstHOL decls)`.
This restates `panToTargetCompileSemanticsX64Executable` for exactly that call. The
compiler-input premises remain on `mainFirstHOL decls`, which the compiler receives; the
semantic premise and the conclusion are about the original declarations `decls`, using
`semanticsDecls_mainFirstHOL` (which needs a `main` function: without one,
`mainFirstHOL` inserts a default `main` and the semantics differ). Untagged Flapjack
corollary; HOL has no x86-64 Pancake driver theorem. It does not establish that the CLI
performs this call or how it obtains `decls` from source text.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.X64Config Flapjack.Compiler.Encoders.X64
open Flapjack.Pancake.PanToTarget (mainFirstHOL semanticsDecls_mainFirstHOL)

/-- The x86-64 Pancake correctness theorem with the compiler premise on the assembler-only
callable compiler at `pancake_backend_conf x64BackendConfig` and `x64Config`; every other
premise and the conclusion are those of `panToTargetCompileSemanticsX64`
(Flapjack-specific corollary; no HOL original). -/
theorem panToTargetCompileSemanticsX64AsmExecutable {σ : Type}
    (mc : MachineConfig 64 X64State X64Projection)
    (pan_code : List (DeclHOL 64)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 64 σ)
    (ms : X64State) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 64)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isX64MachineConfig mc →
    compileProgMaxAsmExecutable (Flapjack.Compiler.pancakeBackendConf x64BackendConfig)
      x64Config pan_code = (some (bytes, bitmaps, c'), stack_max) ∧
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
          (Flapjack.Compiler.pancakeBackendConf x64BackendConfig).dataConf - 1) ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs (Flapjack.Compiler.pancakeBackendConf x64BackendConfig).stackConf.regNames)
      mc c'.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start pan_code ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL mc ffi ms b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config
          (Flapjack.Compiler.pancakeBackendConf x64BackendConfig) mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start pan_code) b := by
  intro hmc ⟨hcomp, rest⟩
  have hconfig : mc.target.config = x64Config := by rw [hmc.1]; rfl
  rw [← hconfig] at hcomp
  rw [compileProgMaxAsmExecutable_eq] at hcomp
  exact panToTargetCompileSemanticsX64 mc pan_code bytes bitmaps c' stack_max s ms
    globals_size heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start hmc ⟨hcomp, rest⟩

/-- The x86-64 Pancake correctness theorem for the CLI's actual call: the compiler premise
is on `mainFirstHOL decls`, while the semantic premise and the conclusion are about the
original `decls` (Flapjack-specific corollary; no HOL original). -/
theorem panToTargetCompileSemanticsX64Source {σ : Type}
    (mc : MachineConfig 64 X64State X64Projection)
    (decls : List (DeclHOL 64)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 64 σ)
    (ms : X64State) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 64)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isX64MachineConfig mc →
    (∃ fi : FunDeclHOL 64, .function fi ∈ decls ∧ fi.name = ofString "main") →
    compileProgMaxAsmExecutable pancakeX64BackendConfig x64Config (mainFirstHOL decls) =
      (some (bytes, bitmaps, c'), stack_max) ∧
    pancakeGoodCodeHOL (mainFirstHOL decls) = true ∧
    distinctParamsHOL (functionsHOL (mainFirstHOL decls)) ∧
    ((functionsHOL (mainFirstHOL decls)).map Prod.fst).Nodup ∧
    s.code = HolFiniteMapExact.empty ∧
    s.locals = HolFiniteMapExact.empty ∧
    s.globals = HolFiniteMapExact.empty ∧
    sizeOfEidsHOL (mainFirstHOL decls) < 2 ^ 64 ∧
    s.eshapes = HolFiniteMapExact.empty ∧
    (0 : BitVec 64) < mc.target.getReg ms mc.lenReg ∧
    globals_size =
      (let dec_shs := decShapesHOL (mainFirstHOL decls)
       let struct_ctxt := decsStcnamesHOLExact (width := 64) [] (mainFirstHOL decls)
       (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
    mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.lenReg = s.baseAddr ∧
    globalsAllocatableHOL s (mainFirstHOL decls) ∧
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
        (2 * DataToWord.maxHeapLimit 64 pancakeX64BackendConfig.dataConf - 1) ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs pancakeX64BackendConfig.stackConf.regNames)
      mc c'.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start decls ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL mc ffi ms b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config pancakeX64BackendConfig mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start decls) b := by
  intro hmc hasMain ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes,
    hpos, hsize, hlt, hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4,
    hlo, hhi, hheap, hffi, hbe, hinst, hstart, hfail⟩
  have hsem := semanticsDecls_mainFirstHOL s start decls hasMain
  rw [← hsem] at hfail ⊢
  exact panToTargetCompileSemanticsX64AsmExecutable mc (mainFirstHOL decls) bytes bitmaps c'
    stack_max s ms globals_size heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start hmc
    ⟨hcomp, hgood, hparams, hnodup, hcode, hlocals, hglobals, heids, heshapes, hpos, hsize, hlt,
      hbase, halloc, hheapLen, htop, hglobLe, hmemaddrs, halign, hadj2, hadj4, hlo, hhi, hheap,
      hffi, hbe, hinst, hstart, hfail⟩

end Flapjack.Pancake.Proofs.PanToTarget

import Flapjack.RiscV.NativeSource
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxAsmWith
import Flapjack.Pancake.Proofs.PanToTarget.RiscVSource

/-!
# Correctness of the parser-backed native RISC-V compiler

`Flapjack.RiscV.NativeSource.compile` parses and statically checks Pancake source text,
then compiles `mainFirstHOL` of the parsed declarations with `compileProgAsmFast` at
`pancake_backend_conf riscv_backend_config` and `riscv_config`, keeping only the compiled
artifact. This module derives the concrete RISC-V correctness theorem for that driver: when
it succeeds with a compiled tuple and the parsed program has a `main` function, every
machine behaviour of the installed code is, up to the original resource-limit relaxation,
the Pancake semantics of the parsed declarations. Parse and static errors are separate
driver outcomes with no correctness claim; the default-`main` case (no `main` function) is
excluded because `mainFirstHOL` then inserts a function. The remaining premises are the
original non-configuration premises of `pan_to_target_compile_semantics` on the compiled
declarations `out.declarations`. Untagged Flapjack theorem; HOL has no Pancake RISC-V
driver theorem. The CLI linkage is in `NativeCLICorrect`.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.RiscVConfig Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Pancake.PanToTarget (mainFirstHOL)

/-- The logical stack bound of the full compiler on the recorded declarations.
This proof API is separate from `NativeSource.Output`: ordinary compilation does not
compute it. Flapjack infrastructure, not a new HOL declaration. -/
def nativeSourceLogicalBound (out : RiscV.NativeSource.Output) : Option Nat :=
  (compileProgMaxAsmExecutable pancakeRiscVBackendConfig riscvConfig out.declarations).2

/-- The no-depth driver artifact is the first projection of the full logical compiler,
for every parsed input, including failure (Flapjack infrastructure). -/
theorem nativeSourceCompileDeclarations_eq (parsed : List (Decl (BitVec 64))) :
    RiscV.NativeSource.compileDeclarations parsed =
      (compileProgMaxAsmExecutable pancakeRiscVBackendConfig riscvConfig
        (mainFirstHOL (parsed.map declToHOL))).1 := by
  unfold RiscV.NativeSource.compileDeclarations
  exact compileProgAsmFast_eq_fst _ _ _

/-- A successful driver run comes from a successful parse and static check, records
`mainFirstHOL` of the parsed declarations and the native artifact compiler's result on them
(Flapjack infrastructure). -/
theorem nativeSourceCompile_ok {source : String} {out : RiscV.NativeSource.Output}
    (compiled : RiscV.NativeSource.compile source = .ok out) :
    ∃ parsed : List (Decl (BitVec 64)),
      Parser.parseTopDecs (fun value => BitVec.ofInt 64 value) source = .ok parsed ∧
      out.declarations = mainFirstHOL (parsed.map declToHOL) ∧
      out.artifact = RiscV.NativeSource.compileDeclarations parsed := by
  unfold RiscV.NativeSource.compile at compiled
  split at compiled
  · simp at compiled
  · rename_i parsed parsedEq
    dsimp only at compiled
    split at compiled
    · simp at compiled
    · simp only [Except.ok.injEq] at compiled
      exact ⟨parsed, parsedEq, by rw [← compiled], by rw [← compiled]⟩

/-- Every successful artifact has the full logical compiler result with its logical
bound. This links emitted bytes to the full compiler without evaluating depth in the
CLI (Flapjack infrastructure). -/
theorem nativeSourceCompile_full_result {source : String} {out : RiscV.NativeSource.Output}
    (compiled : RiscV.NativeSource.compile source = .ok out) :
    compileProgMaxAsmExecutable pancakeRiscVBackendConfig riscvConfig out.declarations =
      (out.artifact, nativeSourceLogicalBound out) := by
  obtain ⟨parsed, _, declsEq, resultEq⟩ := nativeSourceCompile_ok compiled
  apply Prod.ext
  · rw [resultEq, nativeSourceCompileDeclarations_eq, declsEq]
  · rfl

/-- Concrete RISC-V correctness of the parser-backed native compiler: if
`NativeSource.compile source` succeeds with compiled bytes, bitmaps and configuration,
`stack_max` is its full compiler's logical bound, the parsed program has a `main` function,
and the original non-configuration
premises hold of the compiled declarations, then every behaviour of the installed machine
code relates to the Pancake semantics of the parsed declarations (Flapjack-specific; no HOL
original). -/
theorem nativeSourceCompile_correct {σ : Type} {source : String}
    {out : RiscV.NativeSource.Output} (parsed : List (Decl (BitVec 64)))
    (compiled : RiscV.NativeSource.compile source = .ok out)
    (parsedEq : Parser.parseTopDecs (fun value => BitVec.ofInt 64 value) source = .ok parsed)
    (mc : MachineConfig 64 RiscV.L3.riscv_state RiscVProjection)
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 64 σ)
    (ms : RiscV.L3.riscv_state) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 64)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS) :
    isRiscvMachineConfig mc →
    (∃ fi : FunDeclHOL 64, .function fi ∈ parsed.map declToHOL ∧ fi.name = ofString "main") →
    out.artifact = some (bytes, bitmaps, c') ∧
    stack_max = nativeSourceLogicalBound out ∧
    pancakeGoodCodeHOL out.declarations = true ∧
    distinctParamsHOL (functionsHOL out.declarations) ∧
    ((functionsHOL out.declarations).map Prod.fst).Nodup ∧
    s.code = HolFiniteMapExact.empty ∧
    s.locals = HolFiniteMapExact.empty ∧
    s.globals = HolFiniteMapExact.empty ∧
    sizeOfEidsHOL out.declarations < 2 ^ 64 ∧
    s.eshapes = HolFiniteMapExact.empty ∧
    (0 : BitVec 64) < mc.target.getReg ms mc.lenReg ∧
    globals_size =
      (let dec_shs := decShapesHOL out.declarations
       let struct_ctxt := decsStcnamesHOLExact (width := 64) [] out.declarations
       (dec_shs.map (sizeOfShapeWithContextHOL (holThe struct_ctxt))).sum) ∧
    mc.target.getReg ms mc.lenReg < mc.target.getReg ms mc.ptr2Reg ∧
    mc.target.getReg ms mc.lenReg = s.baseAddr ∧
    globalsAllocatableHOL s out.declarations ∧
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
        (2 * DataToWord.maxHeapLimit 64 pancakeRiscVBackendConfig.dataConf - 1) ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs pancakeRiscVBackendConfig.stackConf.regNames)
      mc c'.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start (parsed.map declToHOL) ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL mc ffi ms b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config pancakeRiscVBackendConfig mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start (parsed.map declToHOL)) b := by
  intro hmc hasMain ⟨hartifact, hbound, rest⟩
  obtain ⟨parsed', parsedEq', declsEq, resultEq⟩ := nativeSourceCompile_ok compiled
  rw [parsedEq] at parsedEq'
  cases Except.ok.inj parsedEq'
  rw [declsEq] at rest
  rw [resultEq, nativeSourceCompileDeclarations_eq] at hartifact
  have hcomp : compileProgMaxAsmExecutable pancakeRiscVBackendConfig riscvConfig
      (mainFirstHOL (parsed.map declToHOL)) = (some (bytes, bitmaps, c'), stack_max) := by
    apply Prod.ext
    · exact hartifact
    · simpa only [nativeSourceLogicalBound, declsEq] using hbound.symm
  exact panToTargetCompileSemanticsRiscVSource mc (parsed.map declToHOL) bytes bitmaps c'
    stack_max s ms globals_size heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start hmc hasMain
    ⟨hcomp, rest⟩

end Flapjack.Pancake.Proofs.PanToTarget

import Flapjack.Pancake.Proofs.PanToTarget.X64NativeSourceCorrect
import Flapjack.X64.NativeCLIAdapter

/-!
# Correctness of `flapjack-compile --target=x64` output

`flapjack-compile --target=x64` prints `X64.NativeCLI.output format source`: the
rendering of the artifact of `X64.NativeSource.compile source`. This module states, for
every successful run, that the printed text is the rendering of a compiled tuple whose
bytes, bitmaps and configuration, together with its logical stack bound, satisfy the
concrete x86-64 correctness theorem for the parsed program. Untagged Flapjack theorem;
HOL has no Pancake driver theorem.
-/

namespace Flapjack.Pancake.Proofs.PanToTarget

open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Compiler.Backend.X64Config Flapjack.Compiler.Encoders.X64

/-- The concrete x86-64 correctness of a native driver run `out` on the parsed program
`parsed`: the conclusion of `x64NativeSourceCompile_correct`, for every machine
configuration, state and the original non-configuration premises. -/
def NativeX64Correctness (parsed : List (Decl (BitVec 64)))
    (out : X64.NativeSource.Output) : Prop :=
  ∀ {σ : Type} (mc : MachineConfig 64 X64State X64Projection)
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (c' : Backend.Config) (stack_max : Option Nat) (s : PanSemStateFiniteExact 64 σ)
    (ms : X64State) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec 64)
    (ffi : HolFfiState σ) (cbspace data_sp : Nat) (start : MlS),
    isX64MachineConfig mc →
    (∃ fi : FunDeclHOL 64, .function fi ∈ parsed.map declToHOL ∧ fi.name = ofString "main") →
    out.artifact = some (bytes, bitmaps, c') ∧
    stack_max = x64NativeSourceLogicalBound out ∧
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
        (2 * DataToWord.maxHeapLimit 64 pancakeX64BackendConfig.dataConf - 1) ∧
    s.ffi = ffi ∧ mc.target.config.bigEndian = s.be ∧
    panInstalled bytes cbspace bitmaps data_sp c'.labConf.ffiNames
      (heapRegs pancakeX64BackendConfig.stackConf.regNames)
      mc c'.labConf.shmemExtra ms (wlabWlocExact ∘ s.memory) s.memaddrs s.shMemaddrs ∧
    start = ofString "main" ∧
    PanSemStateFiniteExact.semanticsDecls s start (parsed.map declToHOL) ≠ HolBehaviour.fail →
    ∀ b, machineSemHOL mc ffi ms b →
      extendWithResourceLimitPrimeHOL
        (optionLt stack_max (some (readLimits mc.target.config pancakeX64BackendConfig mc ms).1))
        (fun b' => b' = PanSemStateFiniteExact.semanticsDecls s start (parsed.map declToHOL)) b

/-- x86-64 CLI correctness: every successful `flapjack-compile --target=x64` run (any
output mode) prints the rendering of a compiled artifact `(bytes, bitmaps, config)` of
`NativeSource.compile` on a successfully parsed program, and that run satisfies the
concrete x86-64 correctness theorem `NativeX64Correctness` for the parsed program; in
particular the emitted code is `bytes` (Flapjack-specific; no HOL original). -/
theorem x64CLIOutput_correct {format : RiscV.NativeCLI.Format} {source : String}
    {warnings : List String} {text : String}
    (succeeded : X64.NativeCLI.output format source = .ok (warnings, text)) :
    ∃ (parsed : List (Decl (BitVec 64))) (out : X64.NativeSource.Output)
        (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64)) (config : Backend.Config),
      Parser.parseTopDecs (fun value => BitVec.ofInt 64 value) source = .ok parsed ∧
      X64.NativeSource.compile source = .ok out ∧
      out.artifact = some (bytes, bitmaps, config) ∧
      text = X64.NativeCLI.render format out.declarations bytes bitmaps config ∧
      compileProgMaxAsmExecutable pancakeX64BackendConfig x64Config out.declarations =
        (some (bytes, bitmaps, config), x64NativeSourceLogicalBound out) ∧
      NativeX64Correctness parsed out := by
  obtain ⟨out, bytes, bitmaps, config, compiled, result, rendered⟩ :=
    X64.NativeCLI.output_ok succeeded
  obtain ⟨parsed, parsedEq, -, -⟩ := x64NativeSourceCompile_ok compiled
  refine ⟨parsed, out, bytes, bitmaps, config, parsedEq, compiled, result, rendered, ?_, ?_⟩
  · simpa only [result] using x64NativeSourceCompile_full_result compiled
  · intro σ mc bytes' bitmaps' c' stack_max s ms globals_size heap_len adj_ptr2 adj_ptr4 ffi
      cbspace data_sp start hmc hasMain premises
    exact x64NativeSourceCompile_correct parsed compiled parsedEq mc bytes' bitmaps' c' stack_max s ms
      globals_size heap_len adj_ptr2 adj_ptr4 ffi cbspace data_sp start hmc hasMain premises

end Flapjack.Pancake.Proofs.PanToTarget

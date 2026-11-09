module

public import Flapjack.X64.NativeSource
public import Flapjack.RiscV.NativeCLIAdapter

@[expose] public section

/-! # Rendering the x86-64 compiler result

The command-line output of the x86-64 driver: a GNU assembler file following
CakeML's `x64_export` (`cakeml/compiler/backend/x64/export_x64Script.sml`) with
`ret = F` and `pk = T` (the Pancake configuration), the raw code bytes, or the
code sections.

`cml_main` passes the entry address in `%rdi`, the heap start in `%rsi`, the
stack start in `%rdx` and the stack end in `%rcx`.  Each FFI stub, `cake_clear`
and `cake_exit` is a 16-byte block before `cake_main`.  The file exports
`cml_heap`, `cml_stack` and `cml_stackend` for the runtime to fill, and ends
with the Windows calling-convention compatibility block.

Flapjack driver infrastructure; no HOL declaration. -/

namespace Flapjack.X64.NativeCLI
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend

/-- `compile_prog`'s function-name table for the main-first declarations at x86-64. -/
def compileProgNames (prog1 : List (DeclHOL 64)) : Spt MlString :=
  let prog2 := panToWordCompileProgHOL
    Flapjack.Compiler.Encoders.X64.x64Config.isa prog1
  let names := sptFromAList ((Flapjack.Basis.Pure.MlList.sort
    (fun a b : Nat => decide (a < b)) (prog2.map Prod.fst)).zip
    (ofString "generated_main" :: (functionsHOL prog1).map Prod.fst))
  sptUnion (sptFromAList
    (WordToStack.stubNames () ++ StackAlloc.stubNames () ++ StackRemove.stubNames ())) names

/-- The Windows calling-convention trampolines for the FFI stubs. -/
def windowsFfiLines (ffiNames : List String) : List String :=
  ffiNames.reverse.flatMap (fun name =>
    [s!"windows_ffi{name}:",
     "     movq    %rcx, %r9",
     "     movq    %rdx, %r8",
     "     movq    %rsi, %rdx",
     "     movq    %rdi, %rcx",
     s!"     jmp     cdecl(ffi{name})",
     ""])

/-- The Windows calling-convention trampolines for `cml_clear` and `cml_exit`
(`ret = false`, the Pancake configuration). -/
def windowsRuntimeLines : List String :=
  ["windows_cml_clear:",
   "     movq    %rcx, %r9",
   "     movq    %rdx, %r8",
   "     movq    %rsi, %rdx",
   "     movq    %rdi, %rcx",
   "     jmp     cdecl(cml_clear)",
   "windows_cml_exit:",
   "     movq    %rcx, %r9",
   "     movq    %rdx, %r8",
   "     movq    %rsi, %rdx",
   "     movq    %rdi, %rcx",
   "     callq   cdecl(cml_exit)"]

/-- The `x86_64` assembly frame around the code bytes, following `x64_export`
with `ret = false` and `pk = true`. -/
def assemblyFrame (ffiNames : List String) (bytes : List (BitVec 8))
    (bitmaps : List Nat) (symbolLines : List String) : String :=
  let ffiStubLines := ffiNames.reverse.flatMap (fun name =>
    [s!"cake_ffi{name}:", "     pushq   %rax", s!"     jmp     wcdecl(ffi{name})",
     "     .p2align 4", ""])
  String.intercalate "\n"
    (RiscV.pancakePrologue ++
      ["", "     .file        \"cake.S\"", "", "     .data",
       "     .p2align 3", "cdecl(cml_heap): .quad 0",
       "cdecl(cml_stack): .quad 0", "cdecl(cml_stackend): .quad 0",
       "     .p2align 3", "cake_bitmaps:"] ++
      RiscV.assemblyBitmapLines bitmaps ++
      ["     .globl cdecl(cake_bitmaps_buffer_begin)",
       "cdecl(cake_bitmaps_buffer_begin):", "#if defined(EVAL)",
       "     .space DATA_BUFFER_SIZE", "#endif",
       "     .globl cdecl(cake_bitmaps_buffer_end)",
       "cdecl(cake_bitmaps_buffer_end):",
       "", "/* Start up code */", "", "     .text", "     .p2align 12",
       "     .globl  cdecl(cake_text_begin)", "cdecl(cake_text_begin):",
       "     .globl  cdecl(cml_main)", "     .globl  cdecl(cml_heap)",
       "     .globl  cdecl(cml_stack)", "     .globl  cdecl(cml_stackend)",
       "#if defined(__APPLE__)", "", "#elif defined(__WIN32)",
       "     .func   cml_main", "#else", "     .type   cml_main, function", "#endif",
       "cdecl(cml_main):",
       "     pushq   %rbp                            # push base pointer",
       "     movq    %rsp, %rbp                      # save stack pointer",
       "     leaq    cake_main(%rip), %rdi           # arg1: entry address",
       "     movq    cdecl(cml_heap)(%rip), %rsi     # arg2: first address of heap",
       "     movq    cdecl(cml_stack)(%rip), %rdx    # arg3: first address of stack",
       "     movq    cdecl(cml_stackend)(%rip), %rcx # arg4: first address past the stack",
       "     jmp     cake_main",
       "", "#if defined(__WIN32)", "     .endfunc", "#endif",
       "/* CakeML FFI interface (each block is 16 bytes long) */", "",
       "     .p2align 4", ""] ++
      ffiStubLines ++
      ["cake_clear:", "     pushq   %rax", "     pushq   %rdi",
       "     callq   wcdecl(cml_clear)", "     popq    %rdi", "     ret",
       "     .p2align 4", "",
       "cake_exit:", "     callq   cdecl(cml_exit)", "     .p2align 4", "",
       "cake_main:", "", "/* Generated machine code follows */", ""] ++
      RiscV.assemblyByteLines bytes ++
      ["     .globl cdecl(cake_codebuffer_begin)",
       "cdecl(cake_codebuffer_begin):", "#if defined(EVAL)",
       "     .space CODE_BUFFER_SIZE", "#endif", "     .p2align 12",
       "     .globl cdecl(cake_codebuffer_end)",
       "cdecl(cake_codebuffer_end):", "     .space 4096"] ++
      symbolLines ++
      ["", "/* Windows Compatibility for CakeML FFI interface */", ""] ++
      windowsFfiLines ffiNames ++ windowsRuntimeLines ++ [""])

/-- The assembly file for a compiled tuple. -/
def assembly (prog1 : List (DeclHOL 64)) (bytes : List (BitVec 8))
    (bitmaps : List (BitVec 64)) (config : Backend.Config) : String :=
  assemblyFrame
    ((Backend.ffinamesToStringList (config.labConf.ffiNames.getD [])).map toStringOfBytes)
    bytes (bitmaps.map BitVec.toNat)
    (RiscV.NativeCLI.symbolLines
      (RiscV.NativeCLI.exportSymbols (compileProgNames prog1) config))

/-- The rendered standard output for a compiled tuple. -/
def render (format : RiscV.NativeCLI.Format) (declarations : List (DeclHOL 64))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64)) (config : Backend.Config) : String :=
  match format with
  | .assembly => assembly declarations bytes bitmaps config
  | .hex => RiscV.NativeCLI.hexBytes bytes ++ "\n"
  | .sections =>
      String.join ((RiscV.sectionsOfSymbols (width := 64) bytes config.labConf.secPosLen).map
        fun entry => s!"{entry.label} {entry.address.toNat} " ++
          RiscV.NativeCLI.hexBytes entry.bytes ++ "\n")

/-- The whole x86-64 CLI run on source text: the warnings and standard output,
or the error message. Parse and static errors and backend failure are errors. -/
def output (format : RiscV.NativeCLI.Format) (source : String) :
    Except String (List String × String) :=
  match NativeSource.compile source with
  | .error error => .error (NativeSource.sourceErrorDescription error)
  | .ok out =>
      match out.artifact with
      | none => .error "x86-64 backend compilation failed"
      | some (bytes, bitmaps, config) =>
          .ok (out.warnings.map (fun warning => s!"{repr warning}"),
            render format out.declarations bytes bitmaps config)

/-- A successful x86-64 CLI run comes from a successful `NativeSource.compile`
whose whole tuple is compiled, and its output is that tuple's rendering
(Flapjack infrastructure). -/
theorem output_ok {format : RiscV.NativeCLI.Format} {source : String} {warnings : List String}
    {text : String} (succeeded : output format source = .ok (warnings, text)) :
    ∃ (out : NativeSource.Output) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
        (config : Backend.Config),
      NativeSource.compile source = .ok out ∧
      out.artifact = some (bytes, bitmaps, config) ∧
      text = render format out.declarations bytes bitmaps config := by
  unfold output at succeeded
  split at succeeded
  · simp at succeeded
  · rename_i out compiled
    split at succeeded
    · simp at succeeded
    · rename_i bytes bitmaps config result
      simp only [Except.ok.injEq, Prod.mk.injEq] at succeeded
      exact ⟨out, bytes, bitmaps, config, compiled, result, succeeded.2.symm⟩

end Flapjack.X64.NativeCLI

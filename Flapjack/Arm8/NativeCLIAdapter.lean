import Flapjack.Arm8.NativeSource
import Flapjack.RiscV.NativeCLIAdapter

/-! # Rendering the ARMv8 (AArch64) compiler result

The command-line output of the ARMv8 driver: a GNU assembler file following CakeML's
`arm8_export` (`cakeml/compiler/backend/arm8/export_arm8Script.sml`) with `ret = F` and
`pk = T` (the Pancake configuration), the raw code bytes, or the code sections.

The startup code loads the entry address and the heap, stack and stack-end pointers into
`x0`-`x3` and branches to `cake_main`; each FFI stub, `cake_clear` and `cake_exit` is one
16-byte block branching to the C function `ffi<name>` or `cml_exit`.  The frame exports
`cml_heap`, `cml_stack` and `cml_stackend` for the runtime to fill before calling
`cml_main`.

Flapjack driver infrastructure; no HOL declaration. -/

namespace Flapjack.Arm8.NativeCLI
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend

/-- `compile_prog`'s function-name table for the main-first declarations at ARMv8. -/
def compileProgNames (prog1 : List (DeclHOL 64)) : Spt MlString :=
  let prog2 := panToWordCompileProgHOL
    Flapjack.Compiler.Encoders.Arm8.arm8Config.isa prog1
  let names := sptFromAList ((Flapjack.Basis.Pure.MlList.sort
    (fun a b : Nat => decide (a < b)) (prog2.map Prod.fst)).zip
    (ofString "generated_main" :: (functionsHOL prog1).map Prod.fst))
  sptUnion (sptFromAList
    (WordToStack.stubNames () ++ StackAlloc.stubNames () ++ StackRemove.stubNames ())) names

/-- The `aarch64` assembly frame around the code bytes. -/
def assemblyFrame (ffiNames : List String) (bytes : List (BitVec 8))
    (bitmaps : List Nat) (symbolLines : List String) : String :=
  let ffiStubLines := ffiNames.reverse.flatMap (fun name =>
    [s!"cake_ffi{name}:", s!"     b     cdecl(ffi{name})", "     .p2align 4", ""])
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
       "cdecl(cake_bitmaps_buffer_end):", "", "/* Start up code */", "",
       "     .text", "     .p2align 3", "     .globl  cdecl(cml_main)",
       "     .globl  cdecl(cml_heap)", "     .globl  cdecl(cml_stack)",
       "     .globl  cdecl(cml_stackend)", "#ifndef __APPLE__",
       "     .type   cml_main, function", "#endif", "",
       ".macro _ldrel reg sym", "#ifdef __APPLE__",
       "adrp \\reg, \\sym@PAGE", "add  \\reg, \\reg, \\sym@PAGEOFF",
       "#else", "adrp \\reg, \\sym", "add  \\reg, \\reg, :lo12:\\sym",
       "#endif", ".endm", "",
       "cdecl(cml_main):",
       "     _ldrel x0, cake_main            /* arg1: entry address */",
       "     _ldrel x1, cdecl(cml_heap)      /* arg2: first address of heap */",
       "     ldr    x1,[x1]",
       "     _ldrel x2, cdecl(cml_stack)     /* arg3: first address of stack */",
       "     ldr    x2,[x2]",
       "     _ldrel x3, cdecl(cml_stackend)  /* arg4: first address past the stack */",
       "     ldr    x3,[x3]",
       "     b      cake_main",
       "     .ltorg", "",
       "/* CakeML FFI interface (each block is 16 bytes long) */", "",
       "     .p2align 4", ""] ++
      ffiStubLines ++
      ["cake_clear:", "     b   cdecl(cml_exit)", "     .p2align 4", "",
       "cake_exit:", "     b   cdecl(cml_exit)", "     .p2align 4", "",
       "cake_main:", "", "/* Generated machine code follows */", ""] ++
      RiscV.assemblyByteLines bytes ++
      ["     .globl cdecl(cake_codebuffer_begin)",
       "cdecl(cake_codebuffer_begin):", "#if defined(EVAL)",
       "     .space CODE_BUFFER_SIZE", "#endif", "     .p2align 12",
       "     .globl cdecl(cake_codebuffer_end)",
       "cdecl(cake_codebuffer_end):", "     .space 4096"] ++
      symbolLines ++ [""])

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

/-- The whole ARMv8 CLI run on source text: the warnings and standard output, or the error
message. Parse and static errors and backend failure are errors. -/
def output (format : RiscV.NativeCLI.Format) (source : String) :
    Except String (List String × String) :=
  match NativeSource.compile source with
  | .error error => .error (NativeSource.sourceErrorDescription error)
  | .ok out =>
      match out.artifact with
      | none => .error "ARMv8 backend compilation failed"
      | some (bytes, bitmaps, config) =>
          .ok (out.warnings.map (fun warning => s!"{repr warning}"),
            render format out.declarations bytes bitmaps config)

/-- A successful ARMv8 CLI run comes from a successful `NativeSource.compile` whose whole
tuple is compiled, and its output is that tuple's rendering (Flapjack infrastructure). -/
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

end Flapjack.Arm8.NativeCLI

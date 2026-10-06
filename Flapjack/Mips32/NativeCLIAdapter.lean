import Flapjack.Mips32.NativeSource
import Flapjack.RiscV.NativeCLIAdapter

/-! # Rendering the MIPS32 (Ziren) compiler result

The command-line output of the MIPS32 driver: a GNU assembler file for `mipsel` following
CakeML's MIPS export (`cakeml/compiler/backend/mips/export_mipsScript.sml`) at 32 bits, the
raw code bytes, or the code sections.

The assembly file is assembled with `.set noreorder`, so every jump in the startup code and
the stubs has an explicit delay slot. As in CakeML's MIPS export, `cml_main` passes the entry
address, the first heap address, the first stack address and the first address past the stack
in `$a0`-`$a3`. Each FFI stub, `cake_clear` and `cake_exit` is one 16-byte block (`la`
expands to `lui`/`addiu`, then `jr` and a `nop`) jumping to the C (or Rust) function
`ffi<name>`, `cml_exit`. The frame exports `cml_heap`, `cml_stack` and `cml_stackend` for the
runtime to fill before calling `cml_main`.

Flapjack driver infrastructure; no HOL declaration. -/

namespace Flapjack.Mips32.NativeCLI
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend

/-- `compile_prog`'s function-name table for the main-first declarations at MIPS32. -/
def compileProgNames (prog1 : List (DeclHOL 32)) : Spt MlString :=
  let prog2 := panToWordCompileProgHOL
    Flapjack.Compiler.Encoders.Mips32.mips32Config.isa prog1
  let names := sptFromAList ((Flapjack.Basis.Pure.MlList.sort
    (fun a b : Nat => decide (a < b)) (prog2.map Prod.fst)).zip
    (ofString "generated_main" :: (functionsHOL prog1).map Prod.fst))
  sptUnion (sptFromAList
    (WordToStack.stubNames () ++ StackAlloc.stubNames () ++ StackRemove.stubNames ())) names

/-- The `mipsel` assembly frame around the code bytes. -/
def assemblyFrame (ffiNames : List String) (bytes : List (BitVec 8))
    (symbolLines : List String) : String :=
  let jumpTo (target : String) : List String :=
    [s!"     la      $t9,cdecl({target})", "     jr      $t9", "     nop", "     .p2align 4", ""]
  let ffiStubLines := ffiNames.reverse.flatMap (fun name =>
    s!"cake_ffi{name}:" :: jumpTo s!"ffi{name}")
  String.intercalate "\n"
    (RiscV.pancakePrologue ++
      ["", "     .file        \"cake.S\"", "     .set noreorder", "", "     .data",
       "     .p2align 2", "     .globl  cdecl(cml_heap)", "     .globl  cdecl(cml_stack)",
       "     .globl  cdecl(cml_stackend)",
       "cdecl(cml_heap): .word 0", "cdecl(cml_stack): .word 0", "cdecl(cml_stackend): .word 0",
       "", "#### Start up code", "",
       "     .text", "     .p2align 3", "     .globl  cdecl(cml_main)",
       "     .type   cml_main, function",
       "cdecl(cml_main):",
       "     la      $a0,cake_main           # arg1: entry address",
       "     lw      $a1,cdecl(cml_heap)     # arg2: first address of heap",
       "     lw      $a2,cdecl(cml_stack)    # arg3: first address of stack",
       "     lw      $a3,cdecl(cml_stackend) # arg4: first address past the stack",
       "     j       cake_main",
       "     nop", "",
       "#### CakeML FFI interface (each block is 16 bytes long)", "",
       "     .p2align 4", ""] ++ ffiStubLines ++
      ("cake_clear:" :: jumpTo "cml_exit") ++
      ("cake_exit:" :: jumpTo "cml_exit") ++
      ["cake_main:", "", "#### Generated machine code follows", ""]
      ++ RiscV.assemblyByteLines bytes
      ++ ["     .globl cdecl(cake_codebuffer_begin)",
          "cdecl(cake_codebuffer_begin):", "     .p2align 12",
          "     .globl cdecl(cake_codebuffer_end)",
          "cdecl(cake_codebuffer_end):", "     .space 4096"]
      ++ symbolLines
      ++ [""])

/-- The assembly file for a compiled tuple. -/
def assembly (prog1 : List (DeclHOL 32)) (bytes : List (BitVec 8)) (config : Backend.Config) :
    String :=
  assemblyFrame
    ((Backend.ffinamesToStringList (config.labConf.ffiNames.getD [])).map toStringOfBytes)
    bytes
    (RiscV.NativeCLI.symbolLines
      (RiscV.NativeCLI.exportSymbols (compileProgNames prog1) config))

/-- The rendered standard output for a compiled tuple. -/
def render (format : RiscV.NativeCLI.Format) (declarations : List (DeclHOL 32))
    (bytes : List (BitVec 8)) (config : Backend.Config) : String :=
  match format with
  | .assembly => assembly declarations bytes config
  | .hex => RiscV.NativeCLI.hexBytes bytes ++ "\n"
  | .sections =>
      String.join ((RiscV.sectionsOfSymbols (width := 32) bytes config.labConf.secPosLen).map
        fun entry => s!"{entry.label} {entry.address.toNat} " ++
          RiscV.NativeCLI.hexBytes entry.bytes ++ "\n")

/-- The whole MIPS32 CLI run on source text: the warnings and standard output, or the error
message. Parse and static errors and backend failure are errors. -/
def output (format : RiscV.NativeCLI.Format) (source : String) :
    Except String (List String × String) :=
  match NativeSource.compile source with
  | .error error => .error (NativeSource.sourceErrorDescription error)
  | .ok out =>
      match out.artifact with
      | none => .error "MIPS32 backend compilation failed"
      | some (bytes, _, config) =>
          .ok (out.warnings.map (fun warning => s!"{repr warning}"),
            render format out.declarations bytes config)

/-- A successful MIPS32 CLI run comes from a successful `NativeSource.compile` whose whole
tuple is compiled, and its output is that tuple's rendering (Flapjack infrastructure). -/
theorem output_ok {format : RiscV.NativeCLI.Format} {source : String} {warnings : List String}
    {text : String} (succeeded : output format source = .ok (warnings, text)) :
    ∃ (out : NativeSource.Output) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 32))
        (config : Backend.Config),
      NativeSource.compile source = .ok out ∧
      out.artifact = some (bytes, bitmaps, config) ∧
      text = render format out.declarations bytes config := by
  unfold output at succeeded
  split at succeeded
  · simp at succeeded
  · rename_i out compiled
    split at succeeded
    · simp at succeeded
    · rename_i bytes bitmaps config result
      simp only [Except.ok.injEq, Prod.mk.injEq] at succeeded
      exact ⟨out, bytes, bitmaps, config, compiled, result, succeeded.2.symm⟩

end Flapjack.Mips32.NativeCLI

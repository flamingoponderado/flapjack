import Flapjack.RiscV.NativeSource
import Flapjack.RiscV.ArtifactFormat
import Flapjack.RiscV.LabToTargetRoute

/-! Rendering the parser-backed native whole compiler result as CLI output.

CakeML's Pancake driver (`compilerScript.sml` `compile_pancake_64`) exports the result of
`pan_to_target$compile_prog` with `export_riscv` (`riscv_export` with `ret = F` by default):
the FFI names `ffinames_to_string_list c.lab_conf.ffi_names`, the code bytes, the bitmap
words and `c.symbols`. `compile_prog` computes the same code and bitmaps as
`compile_prog_max` (`from_word` on Pancake's `perf_calls = F` configuration is
`compile_prog_max`'s word-to-stack and `from_stack`); it differs only in the names it
gives `from_lab`, which become `c.symbols`, and in configuration fields the exporter does not
print. These renderers therefore take the native whole tuple and rebuild `c.symbols` from
`lab_conf.sec_pos_len` with `compile_prog`'s names table. Flapjack driver infrastructure;
no separate HOL declaration. -/

namespace Flapjack.RiscV.NativeCLI
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Backend

/-- `compile_prog`'s function-name table (`pan_to_targetScript.sml:41-47`) for the
main-first declarations at RISC-V: sorted pan-to-word function numbers paired with
`generated_main` and the declared function names, extended by the backend stub names. -/
def compileProgNames (prog1 : List (DeclHOL 64)) : Spt MlString :=
  let prog2 := panToWordCompileProgHOL
    Flapjack.Compiler.Encoders.RiscV.Target.riscvConfig.isa prog1
  let names := sptFromAList ((Flapjack.Basis.Pure.MlList.sort
    (fun a b : Nat => decide (a < b)) (prog2.map Prod.fst)).zip
    (ofString "generated_main" :: (functionsHOL prog1).map Prod.fst))
  sptUnion (sptFromAList
    (WordToStack.stubNames () ++ StackAlloc.stubNames () ++ StackRemove.stubNames ())) names

/-- The exported symbols `from_lab` would record with that names table
(`attach_bitmaps`: `lookup_any n names «NOTFOUND»` over `sec_pos_len`). -/
def exportSymbols (names : Spt MlString) (config : Backend.Config) :
    List (MlString × Nat × Nat) :=
  config.labConf.secPosLen.map fun (name, position, length) =>
    (lookupAny name names (ofString "NOTFOUND"), position, length)

/-- `export$escape_sym_char` (`exportScript.sml:170-175`) on a character code. -/
def escapeSymChar (c : Char) : String :=
  let code := c.toNat
  if (0x61 ≤ code ∧ code ≤ 0x7A) ∨ (0x41 ≤ code ∧ code ≤ 0x5A) ∨
      (0x30 ≤ code ∧ code ≤ 0x39) ∨ code = 0x5F then
    String.singleton c
  else "$" ++ toString code ++ "_"

/-- `get_sym_labels` then `emit_symbols` (`exportScript.sml:177-200`): one `makesym` line
per symbol, labelled `cml_<escaped name>_<index>`. -/
def symbolLines (symbols : List (MlString × Nat × Nat)) : List String :=
  symbols.zipIdx.map fun ((name, start, length), index) =>
    let label := "cml_" ++ String.join ((toStringOfBytes name).toList.map escapeSymChar) ++
      "_" ++ toString index
    s!"    makesym({label}, {start}, {length})"

/-- The Pancake assembly frame for a compiled tuple. -/
def assembly (prog1 : List (DeclHOL 64)) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
    (config : Backend.Config) : String :=
  RiscV.pancakeAssemblyFrame
    ((Backend.ffinamesToStringList (config.labConf.ffiNames.getD [])).map toStringOfBytes)
    bytes (bitmaps.map BitVec.toNat)
    (symbolLines (exportSymbols (compileProgNames prog1) config))

def hexDigit (value : Nat) : Char :=
  if value < 10 then
    Char.ofNat ('0'.toNat + value)
  else
    Char.ofNat ('a'.toNat + value - 10)

def hexByte (value : BitVec 8) : String :=
  let n := value.toNat
  String.ofList [hexDigit (n / 16), hexDigit (n % 16)]

/-- Lowercase hexadecimal bytes separated by single spaces. -/
def hexBytes (values : List (BitVec 8)) : String :=
  String.intercalate " " (values.map hexByte)

/-- CLI output modes. -/
inductive Format where
  | assembly
  | hex
  | sections
  deriving DecidableEq

/-- The rendered standard output for a compiled tuple. -/
def render (format : Format) (declarations : List (DeclHOL 64)) (bytes : List (BitVec 8))
    (bitmaps : List (BitVec 64)) (config : Backend.Config) : String :=
  match format with
  | .assembly => assembly declarations bytes bitmaps config
  | .hex => hexBytes bytes ++ "\n"
  | .sections =>
      String.join ((RiscV.sectionsOfSymbols (width := 64) bytes config.labConf.secPosLen).map
        fun entry => s!"{entry.label} {entry.address.toNat} " ++ hexBytes entry.bytes ++ "\n")

/-- The whole native CLI run on source text: the warnings and standard output, or the error
message. Parse and static errors and backend failure are errors. -/
def output (format : Format) (source : String) : Except String (List String × String) :=
  match RiscV.NativeSource.compile source with
  | .error error => .error (sourceRiscVImageErrorDescription error)
  | .ok out =>
      match out.wholeResult.1 with
      | none => .error "native backend compilation failed"
      | some (bytes, bitmaps, config) =>
          .ok (out.warnings.map (fun warning => s!"{repr warning}"),
            render format out.declarations bytes bitmaps config)

/-- Adapter projection: a successful native CLI run comes from a successful
`NativeSource.compile` whose whole tuple is compiled, and its output is that tuple's
rendering. In particular the emitted code is exactly the tuple's bytes: `--hex` prints
`hexBytes bytes` and the assembly frame's code lines are `bytes`, the bytes of
`nativeSourceCompile_correct` (Flapjack infrastructure). -/
theorem output_ok {format : Format} {source : String} {warnings : List String} {text : String}
    (succeeded : output format source = .ok (warnings, text)) :
    ∃ (out : RiscV.NativeSource.Output) (bytes : List (BitVec 8)) (bitmaps : List (BitVec 64))
        (config : Backend.Config),
      RiscV.NativeSource.compile source = .ok out ∧
      out.wholeResult.1 = some (bytes, bitmaps, config) ∧
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

end Flapjack.RiscV.NativeCLI

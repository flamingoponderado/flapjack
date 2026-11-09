module

public import Flapjack.Compiler.Backend.RegAlloc.Executable
public import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
public import Flapjack.Pancake.PanToTarget
public import Flapjack.Pancake.PanStatic
public import Flapjack.Parser
public import Flapjack.Compiler.Backend.X64Config.BackendConfig
public import Flapjack.Compiler.Encoders.X64.Target

@[expose] public section

/-! The parser-backed x86-64 compiler: the RISC-V driver
`Flapjack.RiscV.NativeSource` at word width 64, with `pancake_backend_conf` of
the x86-64 backend configuration and the x86-64 assembler configuration.
Flapjack driver infrastructure, not a HOL declaration. -/
namespace Flapjack.X64.NativeSource
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Encoders.X64

abbrev Artifact :=
  Option (List (BitVec 8) × List (BitVec 64) × Compiler.Backend.Backend.Config)

/-- Parse or static-check failure of the source. -/
inductive SourceError where
  | parse (errors : List Parser.ParseError)
  | static (error : StatErr)
  deriving Repr

def sourceErrorDescription : SourceError → String
  | .parse errors => s!"parse error: {repr errors}"
  | .static error => s!"static check failed: {repr error}"

structure Output where
  declarations : List (DeclHOL 64)
  artifact : Artifact
  warnings : List StatErr

/-- The x86-64 artifact compiler on already parsed declarations. -/
def compileDeclarations (declarations : List (Decl (BitVec 64))) : Artifact :=
  compileProgAsmFast Compiler.Backend.X64Config.pancakeX64BackendConfig x64Config
    (Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL))

/-- Parse and static-check the source, then compile it to x86-64. -/
def compile (source : String) : Except SourceError Output :=
  match Parser.parseTopDecs (fun value => BitVec.ofInt 64 value) source with
  | .error errors => .error (.parse errors)
  | .ok declarations =>
      let checked := staticCheck declarations
      match checked.1 with
      | .error error => .error (.static error)
      | .ok _ =>
          .ok {
            declarations := Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL)
            artifact := compileDeclarations declarations
            warnings := checked.2
          }

end Flapjack.X64.NativeSource

import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
import Flapjack.Pancake.PanToTarget
import Flapjack.Pancake.PanStatic
import Flapjack.Parser
import Flapjack.Compiler.Backend.Mips32Config.BackendConfig
import Flapjack.Compiler.Encoders.Mips32.Target

/-! The parser-backed MIPS32 (Ziren) compiler: the RISC-V driver
`Flapjack.RiscV.NativeSource` at word width 32, with `pancake_backend_conf` of the MIPS32
backend configuration and the MIPS32 assembler configuration. Flapjack driver
infrastructure, not a HOL declaration. -/
namespace Flapjack.Mips32.NativeSource
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Encoders.Mips32

abbrev Artifact :=
  Option (List (BitVec 8) × List (BitVec 32) × Compiler.Backend.Backend.Config)

/-- Parse or static-check failure of the source. -/
inductive SourceError where
  | parse (errors : List Parser.ParseError)
  | static (error : StatErr)
  deriving Repr

def sourceErrorDescription : SourceError → String
  | .parse errors => s!"parse error: {repr errors}"
  | .static error => s!"static check failed: {repr error}"

structure Output where
  declarations : List (DeclHOL 32)
  artifact : Artifact
  warnings : List StatErr

/-- The MIPS32 artifact compiler on already parsed declarations. -/
def compileDeclarations (declarations : List (Decl (BitVec 32))) : Artifact :=
  compileProgAsmFast Compiler.Backend.Mips32Config.pancakeMips32BackendConfig mips32Config
    (Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL))

/-- Parse and static-check the source, then compile it to MIPS32. -/
def compile (source : String) : Except SourceError Output :=
  match Parser.parseTopDecs (fun value => BitVec.ofInt 32 value) source with
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

end Flapjack.Mips32.NativeSource

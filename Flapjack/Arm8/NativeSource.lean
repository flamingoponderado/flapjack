import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
import Flapjack.Pancake.PanToTarget
import Flapjack.Pancake.PanStatic
import Flapjack.Parser
import Flapjack.Compiler.Backend.Arm8Config.BackendConfig
import Flapjack.Compiler.Encoders.Arm8.Configuration

/-! The parser-backed ARMv8 (AArch64) compiler: the RISC-V driver
`Flapjack.RiscV.NativeSource` at word width 64, with `pancake_backend_conf` of the ARMv8
backend configuration and the ARMv8 assembler configuration. Flapjack driver
infrastructure, not a HOL declaration. -/
namespace Flapjack.Arm8.NativeSource
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Encoders.Arm8

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

/-- The ARMv8 artifact compiler on already parsed declarations. -/
def compileDeclarations (declarations : List (Decl (BitVec 64))) : Artifact :=
  compileProgAsmFast Compiler.Backend.Arm8Config.pancakeArm8BackendConfig arm8Config
    (Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL))

/-- Parse and static-check the source, then compile it to ARMv8. -/
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

end Flapjack.Arm8.NativeSource

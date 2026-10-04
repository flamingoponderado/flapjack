import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
import Flapjack.Pancake.PanToTarget
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.RiscV.PipelineDiagnostics

/-! Parser-backed native artifact interface. The artifact retains failure and final
configuration; the stack bound is kept on the separate logical correctness API.
This is Flapjack driver infrastructure, not a separate HOL declaration. -/
namespace Flapjack.RiscV.NativeSource
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Encoders.RiscV.Target

abbrev Artifact :=
  Option (List (BitVec 8) × List (BitVec 64) × Compiler.Backend.Backend.Config)

/-- Driver metadata accompanies the compiled artifact.
Declarations are the explicit original main-first normalization of parsed input. -/
structure Output where
  declarations : List (DeclHOL 64)
  artifact : Artifact
  warnings : List StatErr

/-- The native artifact compiler without depth analysis on already parsed declarations. -/
def compileDeclarations (declarations : List (Decl (BitVec 64))) : Artifact :=
  compileProgAsmFast Compiler.Backend.RiscVConfig.pancakeRiscVBackendConfig riscvConfig
    (Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL))

/-- Parse and static-check the source before invoking the native artifact compiler.
The artifact retains backend failure. -/
def compile (source : String) : Except SourceRiscVImageError Output :=
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

end Flapjack.RiscV.NativeSource

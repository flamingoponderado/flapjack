import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
import Flapjack.Pancake.PanToTarget
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.Compiler.Encoders.RiscV.Unsupported
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

/-- The same native Pancake route with a caller-supplied backend configuration.
This is driver infrastructure rather than an additional HOL declaration.  The
checked pipeline rejects word programs that `compileNative` would silently
lower to `Skip`, and lab programs whose `Asm` registers the target cannot
encode, before any bytes are produced. -/
def compileWithConfig (config : Compiler.Backend.Backend.Config) (source : String) :
    Except SourceRiscVImageError Output :=
  match Parser.parseTopDecs (fun value => BitVec.ofInt 64 value) source with
  | .error errors => .error (.parse errors)
  | .ok declarations =>
      let checked := staticCheck declarations
      match checked.1 with
      | .error error => .error (.static error)
      | .ok _ =>
          let declarations := Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL)
          match compileProgAsmFastChecked Flapjack.Compiler.Encoders.RiscV.riscvUnsupported
            config riscvConfig declarations with
          | .error (.wordToStack failure) => .error (.wordStackGuard failure)
          | .error (.labEncoding failure) => .error (.labEncodingGuard failure)
          | .error (.labToTarget failure) => .error (.artifactFailure failure)
          | .ok artifact =>
              .ok { declarations := declarations
                    artifact := some artifact
                    warnings := checked.2 }

/-- Parse and static-check the source before invoking the native artifact compiler.
A backend failure is a structured, located artifact error, not a bare missing
artifact.  This is the standard-configuration instance of `compileWithConfig`. -/
def compile (source : String) : Except SourceRiscVImageError Output :=
  compileWithConfig Compiler.Backend.RiscVConfig.pancakeRiscVBackendConfig source

/-- Selecting the standard configuration recovers the existing native
source compiler, including its declarations, artifact, and warnings. -/
theorem compileWithConfig_default (source : String) :
    compileWithConfig Compiler.Backend.RiscVConfig.pancakeRiscVBackendConfig source = compile source := by
  rfl

end Flapjack.RiscV.NativeSource

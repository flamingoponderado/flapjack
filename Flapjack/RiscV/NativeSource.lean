import Flapjack.Compiler.Backend.RegAlloc.Executable
import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileProgMaxDepth
import Flapjack.Pancake.PanToTarget
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.RiscV.PipelineDiagnostics

/-! Parser-backed native whole-compiler interface. The complete compiler result
is retained, including failure, final configuration and the maximum-stack bound.
This is Flapjack driver infrastructure, not a separate HOL declaration. -/
namespace Flapjack.RiscV.NativeSource
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Encoders.RiscV.Target

abbrev WholeResult :=
  Option (List (BitVec 8) × List (BitVec 64) × Compiler.Backend.Backend.Config) × Option Nat

/-- Driver metadata accompanies the whole compiler tuple.
Declarations are the explicit original main-first normalization of parsed input. -/
structure Output where
  declarations : List (DeclHOL 64)
  wholeResult : WholeResult
  warnings : List StatErr

/-- The exact native whole compiler on already parsed declarations. -/
def compileDeclarations (declarations : List (Decl (BitVec 64))) : WholeResult :=
  compileProgMaxAsmDepthExecutable Compiler.Backend.RiscVConfig.pancakeRiscVBackendConfig riscvConfig
    (Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL))

/-- Parse and static-check the source before invoking the native whole compiler.
A backend failure remains in the tuple, rather than being projected or discarded. -/
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
            wholeResult := compileDeclarations declarations
            warnings := checked.2
          }

theorem compileDeclarations_eq (declarations : List (Decl (BitVec 64))) :
    compileDeclarations declarations =
      compileProgMaxAsmExecutable Compiler.Backend.RiscVConfig.pancakeRiscVBackendConfig riscvConfig
        (Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL)) := by
  unfold compileDeclarations
  rw [compileProgMaxAsmDepthExecutable_eq, compileProgMaxAsmFast_eq]

end Flapjack.RiscV.NativeSource

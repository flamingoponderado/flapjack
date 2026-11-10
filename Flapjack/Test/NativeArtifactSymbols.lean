module

public import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
public import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
public import Flapjack.Compiler.Backend.RiscVConfig.Executable
public import Flapjack.Parser
public import Flapjack.Pancake.PanToTarget

-- Checks below run compiled code from these modules.
public meta import Flapjack.Basis.Pure.MlString
public meta import Flapjack.Pancake.Semantics.PanSem.StateExactFiniteMap
public meta import Flapjack.Compiler.Backend.RiscVConfig.Executable
public meta import Flapjack.Compiler.Backend.Semantics.WordSem.Alloc
public meta import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
public meta import Flapjack.Pancake.PanToTarget
public meta import Flapjack.Pancake.Proofs.PanToTarget.ExecutableCompileDefinitions
public meta import Flapjack.Parser
@[expose] public section

/-!
# Real artifact symbols

Pins that the driver artifact pipeline passes the real `compile_prog` name table
to `from_stack`, so the returned configuration records real symbols (function
and runtime-stub names) instead of `NOTFOUND`.  The rendered CLI text is
covered separately by the parity goldens and corpus; this test checks the
configuration the artifact carries.
-/

namespace Flapjack.Test.NativeArtifactSymbols

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target (riscvConfig)
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Basis.Pure.MlString

private def source : String := "fun 1 main() { return 0; }"

private def artifactConfig : Option Backend.Config :=
  match Parser.parseTopDecs (fun value => BitVec.ofInt 64 value) source with
  | .ok declarations =>
      let program := Pancake.PanToTarget.mainFirstHOL (declarations.map declToHOL)
      (compileProgAsmFast Compiler.Backend.RiscVConfig.pancakeRiscVBackendConfig
        riscvConfig program).map fun (_, _, config) => config
  | .error _ => none

-- The recorded table is the real one: no section falls back to NOTFOUND.
#guard
  match artifactConfig with
  | some config => !config.symbols.any fun (name, _, _) => name == ofString "NOTFOUND"
  | none => false

-- The generated main and the runtime stubs are recorded by name.
#guard
  match artifactConfig with
  | some config =>
      config.symbols.any (fun (name, _, _) => name == ofString "generated_main") &&
      config.symbols.any (fun (name, _, _) => name == ofString "_Raise") &&
      config.symbols.any (fun (name, _, _) => name == ofString "_StoreConsts")
  | none => false

end Flapjack.Test.NativeArtifactSymbols

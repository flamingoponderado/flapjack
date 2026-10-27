import Flapjack.Basis.BasisProg
import Flapjack.Compiler.Inference.Infer.Core
import Flapjack.Compiler.Backend.SourceToFlat.FromText
import Flapjack.Compiler.Backend.RiscVConfig.Executable

/-! The complete generated basis has the captured HOL declaration count and
is accepted by the current bounded inferencer. This does not establish full
inference correspondence or machine-code output parity. -/
namespace Flapjack.Test.CakeBasisParity
open Flapjack Flapjack.NamespaceHOL Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Inference.Infer.Core

#guard Flapjack.Basis.BasisProg.basis.length == 96
#guard match inferProgramFuel 1000 1000 Flapjack.Basis.BasisProg.basis with
  | .ok env => (nsLookup env.infV (.short (ofString "print"))).isSome &&
      (nsLookup env.infV (.long (ofString "List") (.short (ofString "map")))).isSome
  | .error _ => false

#guard match Flapjack.Compiler.Backend.SourceToFlat.compileBasisSourceFuel 1000 1000 1000 1000 1000
    Flapjack.Compiler.Backend.RiscVConfig.riscvBackendConfigExecutable [] with
  | .success bytes bitmaps _ => bytes.length == 55864 && bitmaps.length == 1669
  | _ => false

end Flapjack.Test.CakeBasisParity

import Flapjack.Basis.BasisProg
import Flapjack.Compiler.Inference.Infer.Core
import Flapjack.Compiler.Backend.SourceToFlat.FromText
import Flapjack.Compiler.Backend.RiscVConfig.Executable
import Flapjack.Test.BasisCakeBviOracle

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

-- Compare the actual configured frontend with every expression of the pinned
-- HOL compiler's BVI result for the complete standard basis.
#guard match Flapjack.Compiler.Backend.SourceToFlat.compileCakeToBviConfiguredFuel 1000
    Flapjack.Compiler.Backend.RiscVConfig.riscvBackendConfigExecutable.sourceConf
    Flapjack.Compiler.Backend.RiscVConfig.riscvBackendConfigExecutable.closConf
    Flapjack.Compiler.Backend.RiscVConfig.riscvBackendConfigExecutable.bvlConf
    Flapjack.Basis.BasisProg.basis with
  | some (_, _, _, code, _) => Flapjack.Test.BasisCakeBviOracle.matchesCaptured code
  | none => false

#guard match Flapjack.Compiler.Backend.SourceToFlat.compileBasisSourceFuel 1000 1000 1000 1000 1000
    Flapjack.Compiler.Backend.RiscVConfig.riscvBackendConfigExecutable [] with
  | .success bytes bitmaps _ => bytes.length == 55864 && bitmaps.length == 1669
  | _ => false

#guard match Flapjack.Compiler.Backend.SourceToFlat.compileBasisSourceFuel 1000 1000 1000 1000 1000
    Flapjack.Compiler.Backend.RiscVConfig.riscvBackendConfigExecutable
    (ofString "val _ = print \"Hello\";").explode with
  | .success bytes bitmaps _ => !bytes.isEmpty && !bitmaps.isEmpty
  | _ => false

end Flapjack.Test.CakeBasisParity

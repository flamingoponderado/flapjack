module

public import Flapjack.Basis.BasisProg
public import Flapjack.Compiler.Inference.Infer.Core
public import Flapjack.Compiler.Backend.SourceToFlat.FromText
public import Flapjack.Compiler.Backend.RiscVConfig.Executable
public import Flapjack.Test.BasisCakeBviOracle

import all Flapjack.Basis.BasisProg
import all Flapjack.Compiler.Inference.Infer.Core
import all Flapjack.Compiler.Backend.SourceToFlat.FromText
import all Flapjack.Compiler.Backend.RiscVConfig.Executable
import all Flapjack.Test.BasisCakeBviOracle
public meta import Flapjack.Basis.Pure.MlString
public meta import Flapjack.Misc.Location
public meta import Flapjack.NamespaceHOL
public meta import Flapjack.Compiler.Backend.FlatPattern.Config
public meta import Flapjack.Compiler.Inference.Infer
public meta import Flapjack.Compiler.Inference.Unify
public meta import Flapjack.Compiler.Backend.SourceToFlat.ToBvi
public meta import Flapjack.Compiler.Backend.RiscVConfig.Names
public meta import Flapjack.Compiler.Backend.Backend.PrimSrcConfig.Executable
public meta import Flapjack.CakeParser.Frontend
public meta import Flapjack.Compiler.Backend.SourceToFlat.ToRiscV

@[expose] public section

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

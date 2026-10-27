import Flapjack.Basis.BasisProg
import Flapjack.Compiler.Inference.Infer.Core

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

end Flapjack.Test.CakeBasisParity

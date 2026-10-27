import Flapjack.TypeSystemHOL.Environments

/-! Representative cases captured from the pinned HOL type-system definitions.
The capture is regression evidence, not a cross-language equivalence proof. -/
namespace Flapjack.Test.CakeTypeEnvironmentParity
open Flapjack.TypeSystemHOL Flapjack.Basis.Pure.MlString

#guard match deBruijnInc 1 3 (.app [.varDb 0, .varDb 1, .varDb 4] 7) with
  | .app [.varDb 0, .varDb 4, .varDb 7] 7 => true
  | _ => false

#guard match deBruijnSubst 1 [.app [] 5, .varDb 7]
    (.app [.varDb 0, .varDb 1, .varDb 2, .varDb 4] 9) with
  | .app [.varDb 0, .app [] 5, .varDb 7, .varDb 2] 9 => true
  | _ => false

#guard match tveLookup (ofString "x") 0
    (.bindTvar 2 (.bindName (ofString "x") 1 (.app [.varDb 0, .varDb 1] 4) .empty)) with
  | some (1, .app [.varDb 0, .varDb 3] 4) => true
  | _ => false

end Flapjack.Test.CakeTypeEnvironmentParity

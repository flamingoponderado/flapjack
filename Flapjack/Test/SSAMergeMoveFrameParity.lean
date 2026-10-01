import Flapjack.Test.SSAMergeMovesParity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAMergeMoveFrame

namespace Flapjack.Test.SSAMergeMoveFrameParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

-- The ten imported complete tuple fixtures are freshly replayed in the original
-- frame probe. This application checks all four conclusions for arbitrary inputs.
example (names : List Nat) (next : Nat) (leftMap rightMap : Spt Nat)
    (allocated : isAllocVar next) :
    let result := mergeMoves names leftMap rightMap next
    isAllocVar result.2.2.1 ∧ next ≤ result.2.2.1 ∧
      (ssaMapOK next leftMap → ssaMapOK result.2.2.1 result.2.2.2.1) ∧
      (ssaMapOK next rightMap → ssaMapOK result.2.2.1 result.2.2.2.2) :=
  mergeMovesFrame names next leftMap rightMap allocated

end Flapjack.Test.SSAMergeMoveFrameParity

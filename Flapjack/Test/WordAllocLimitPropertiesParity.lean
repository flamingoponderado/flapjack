import Flapjack.Test.WordAllocLimitVarParity
import Flapjack.Compiler.Backend.WordAlloc.Proofs.LimitVar.Properties

namespace Flapjack.Test.WordAllocLimitPropertiesParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc

-- Imported native limit tuples match the freshly replayed original program rows.
-- The actual theorem application retains an arbitrary positive-width program
-- and the original equality premise, with both complete result conjuncts.
example {width : Nat} [NeZero width]
    (program : WordLangProgHOL (BitVec width)) (limit : Nat)
    (hlimit : limitVar program = limit) :
    isAllocVar limit ∧ everyVarHOL (fun x => decide (x < limit)) program = true :=
  limitVarProps program limit hlimit

end Flapjack.Test.WordAllocLimitPropertiesParity

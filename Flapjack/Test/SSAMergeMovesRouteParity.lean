import Flapjack.Compiler.Backend.WordAlloc.ProductionMergeMoves

namespace Flapjack.Test.SSAMergeMovesRouteParity
open Flapjack Flapjack.Compiler.Backend.WordAlloc
-- Universal input and output correspondence is checked on arbitrary lists/states.
example (entries : List (Nat × Nat)) (key : Nat) :
    lookupNatInfo key entries = sptAListLookup key entries := productionMergeMapLookup entries key
end Flapjack.Test.SSAMergeMovesRouteParity

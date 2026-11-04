import Flapjack.Compiler.Backend.WordAlloc.ProductionMergeMoves

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Decoder lookup for arbitrary native trees. Flapjack API correspondence,
not an independent HOL declaration. -/
theorem productionSsaDecodedLookup (tree : Spt Nat) (key : Nat) :
    lookupNatInfo key (sptToAList tree) = sptLookup key tree := by
  rw [productionMergeMapLookup]
  simpa only [sptLookup_sptFromAList] using sptLookup_sptFromAList_sptToAList key tree

end Flapjack.Compiler.Backend.WordAlloc

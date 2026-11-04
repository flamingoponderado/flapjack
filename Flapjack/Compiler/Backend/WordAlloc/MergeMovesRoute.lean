module

public import Flapjack.Compiler.Backend.WordAlloc.SSAMergeMoves

@[expose] public section

namespace Flapjack.Compiler.Backend.WordAlloc

/-- Unconditional input-codec law, including duplicate association keys. -/
theorem mergeMovesInputLookup (entries : List (Nat × Nat)) (key : Nat) :
    sptLookup key (sptFromAList entries) = sptAListLookup key entries :=
  sptLookup_sptFromAList key entries

end Flapjack.Compiler.Backend.WordAlloc

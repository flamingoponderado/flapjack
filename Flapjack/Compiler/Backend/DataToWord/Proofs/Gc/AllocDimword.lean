module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.CombinedStore

@[expose] public section

/-! The saturated allocation-size value used by the GiveUp proof. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- A request for one full word range saturates to the all-ones sentinel. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "alloc_size_dimword"
  (words_as_type_indexed_bitvec)]
theorem allocSize_dimword {width : Nat} [NeZero width] (good : goodDimindex width) :
    (gcAllocSize (2 ^ width) : BitVec width) = -1 := by
  rcases good with h | h <;> subst width <;> norm_num [gcAllocSize]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

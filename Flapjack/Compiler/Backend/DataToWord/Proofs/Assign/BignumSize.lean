module

public import Flapjack.Compiler.Backend.DataToWord.Proofs.Gc.SizeValues

@[expose] public section

/-! Bignum sizing for data-to-word assignment correctness. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Assign
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

/-- On supported word widths, bignum size is its word-digit length plus one. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_assignProofScript.sml" "bignum_size"
  (words_as_type_indexed_bitvec)]
theorem bignumSize_eq {width : Nat} [NeZero width] (i : Int) (good : goodDimindex width) :
    DataSem.bignumSize (decide (width = 64)) i =
      (Misc.Multiword.n2mw i.natAbs : List (BitVec width)).length + 1 := by
  rw [DataSem.bignumSize, n2mw_length_eq_bignumDigits i.natAbs good]
  omega

end Flapjack.Compiler.Backend.DataToWord.Proofs.Assign

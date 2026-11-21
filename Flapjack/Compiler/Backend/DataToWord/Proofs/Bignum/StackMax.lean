module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Env
public import Flapjack.Compiler.Backend.BackendProps

@[expose] public section

/-! Stack-maximum option lemmas used by the data-to-word bignum proofs. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.BackendProps

/-- The maximum with an upper bound is that bound. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "option_le_max_dest"]
theorem optionLe_maxDest (a b : Option Nat) : optionLe a b → wordSemOptionMax a b = b := by
  cases a <;> cases b <;> simp [optionLe, wordSemOptionMax]

/-- The optional maximum is commutative. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_bignumProofScript.sml" "option_map_max_comm"]
theorem optionMap_maxComm (a b : Option Nat) : wordSemOptionMax a b = wordSemOptionMax b a := by
  cases a <;> cases b <;> simp [wordSemOptionMax, Nat.max_comm]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Bignum

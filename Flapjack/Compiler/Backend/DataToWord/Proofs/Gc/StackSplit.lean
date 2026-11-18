module

public import Flapjack.Compiler.Backend.Semantics.WordSem.Env

@[expose] public section

/-! Splitting a stack into its HOL `BUTLASTN` and `LASTN` parts. -/
namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack

/-- HOL `BUTLASTN` and `LASTN` partition a list for every count. -/
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "BUTLASTN_APPEND_LASTN"]
theorem butlastn_append_lastn {α : Type} (n : Nat) (xs : List α) :
    (xs.reverse.drop n).reverse ++ wordSemLastN n xs = xs := by
  simp [wordSemLastN, ← List.reverse_append]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

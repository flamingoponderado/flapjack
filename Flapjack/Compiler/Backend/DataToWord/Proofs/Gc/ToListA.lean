module

public import Flapjack.Misc.Sptree.ToList

@[expose] public section

namespace Flapjack.Compiler.Backend.DataToWord.Proofs.Gc
open Flapjack
@[hol "cakeml/compiler/backend/proofs/data_to_word_gcProofScript.sml" "toListA_mk"]
theorem toListA_mk {α : Type} (a : List α) (t1 t2 : Spt α) (x : α) :
    sptToListA a (sptMkBN t1 t2) = sptToListA a (.bn t1 t2) ∧
    sptToListA a (sptMkBS t1 x t2) = sptToListA a (.bs t1 x t2) := by
  cases t1 <;> cases t2 <;> simp [sptMkBN, sptMkBS, sptToListA]

end Flapjack.Compiler.Backend.DataToWord.Proofs.Gc

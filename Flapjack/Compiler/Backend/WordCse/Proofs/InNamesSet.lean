import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Misc.Sptree

namespace Flapjack.Compiler.Backend.WordCse
open Flapjack Compiler.Encoders.Asm

/-- Original arithmetic fact self-mapping predicate. Every register read by
any of the eight arithmetic constructors must be present as its own canonical
representative; no flattening, successful run, or desired output is assumed. -/
@[hol "cakeml/compiler/backend/proofs/word_cseProofScript.sml" "in_names_set_def"
  (words_as_type_indexed_bitvec)]
def inNamesSet {width : Nat} [NeZero width] (operation : HolArith width)
    (canonical : Spt Nat) : Prop :=
  ∀ register ∈ arithReads operation, sptLookup register canonical = some register

end Flapjack.Compiler.Backend.WordCse

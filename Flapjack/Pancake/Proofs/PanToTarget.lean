import Flapjack.HolRef
import Flapjack.Pancake.Proofs.PanToWord

/-!
The source-level declarations from CakeML's `pan_to_targetProofScript.sml`.
This is the counterpart module for ports from that HOL proof script.
-/

namespace Flapjack

open Flapjack.Pancake.PanLang

/-- Exact port of HOL `pancake_good_code`
    (`cakeml/pancake/proofs/pan_to_targetProofScript.sml:22-23`):
    `pancake_good_code pan_code = EVERY good_panops pan_code`.  The `EVERY`-fold
    is rendered by `.all` over the exact width-indexed `DeclHOL width` carrier,
    reusing the exact `goodPanopsHOL` port from `Proofs/PanToWord.lean`. -/
@[hol "cakeml/pancake/proofs/pan_to_targetProofScript.sml" "pancake_good_code_def"
  (words_as_type_indexed_bitvec)]
def pancakeGoodCodeHOL {width : Nat} [NeZero width]
    (code : List (DeclHOL width)) : Bool :=
  code.all goodPanopsHOL

end Flapjack

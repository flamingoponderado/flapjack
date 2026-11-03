import Mathlib.Data.BitVec

/-!
# HOL `words`: `word_log2`

Counterpart of the pinned `wordsScript.sml` rendering of `word_log2`.  It is
HOL library infrastructure outside the CakeML submodule, so the definition is
untagged; `Nat.log2` agrees with HOL `LOG2` on the positive arguments at which
the ported theorems use it.  Both the closed-model ARM8 rendering and the
Pancake `crep_arith` port use this one definition.
-/

namespace Flapjack

/-- HOL `words$word_log2_def`: `word_log2 w = n2w (LOG2 (w2n w))`. -/
def holWordLog2 {width : Nat} (w : BitVec width) : BitVec width :=
  BitVec.ofNat width (Nat.log2 w.toNat)

end Flapjack

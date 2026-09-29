import Flapjack.HolRef

/-!
Exact port of HOL `misc$shift_seq_def` (`cakeml/misc/miscScript.sml:132-134`),
used by wordSem `evaluate_def`'s `Install` clause to advance the compile
oracle.
-/

namespace Flapjack

/-- Exact HOL `shift_seq_def`: `shift_seq k s = \i. s (i + k)`, polymorphic in
    the sequence's value type as in HOL. -/
@[hol "cakeml/misc/miscScript.sml" "shift_seq_def"]
def holShiftSeq {α : Type} (k : Nat) (s : Nat → α) : Nat → α := fun i => s (i + k)

end Flapjack

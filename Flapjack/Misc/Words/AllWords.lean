module

public import Flapjack.HolRef
public import Mathlib.Data.Set.Basic

@[expose] public section

/-! `all_words` from `cakeml/misc/miscScript.sml`: the set of `n` consecutive
words starting at `base`. -/

namespace Flapjack.Misc.Words

/-- Original `all_words`: the empty set at size zero, and the base word inserted
into the set of the remaining `n` consecutive words, whose base is the successor
word. -/
@[hol "cakeml/misc/miscScript.sml" "all_words_def" (words_as_type_indexed_bitvec)]
def allWords {w : Nat} [NeZero w] (base : BitVec w) : Nat → Set (BitVec w)
  | 0 => ∅
  | n + 1 => Set.insert base (allWords (base + 1) n)

end Flapjack.Misc.Words

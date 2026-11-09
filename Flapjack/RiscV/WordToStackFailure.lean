module

public import Flapjack.RiscV.WordToStack

@[expose] public section

/-!
# Classified Word-to-Stack lowering failures

Flapjack diagnostic infrastructure (no HOL counterpart; HOL `word_to_stack$compile` is
total). The executed bitmap-aware Word-to-Stack lowering
`wordToStackProgWordWithBitmapBuilder` is `Option`-valued: each leaf helper may reject its
input. `wordToStackFirstFailure` searches the program without its bitmap state
(no failure depends on that state), and returns a sequence path and failure kind.
The proof does not establish that this is the lowering's first rejecting leaf.
`wordToStackFirstFailure_complete` proves that every
failed lowering is located, so pipeline callers report a precise path and kind instead of an
empty-path fallback (GitHub issue #1158).
-/

namespace Flapjack.RiscV

/-- The leaf operation of the bitmap-aware Word-to-Stack lowering that rejected its input. -/
inductive WordToStackFailureKind where
  | move | assign | const | arith | inst | get | store | set
  | condition | returnValues | locValue | indirectCall
  | opCurrHeap | install | bufferWrite | ffi | shareInst
  deriving DecidableEq, Repr

end Flapjack.RiscV

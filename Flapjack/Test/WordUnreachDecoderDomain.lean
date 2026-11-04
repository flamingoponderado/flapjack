import Flapjack.Compiler.Backend.WordUnreach.ProductionDecoderDomain

/-! Decoder-boundary regressions, distinct from the unchanged original
word_unreach branch fixtures. Rejected instruction leaves remain failures
unless the original transformation actually removes their containing tail.
-/

namespace Flapjack.Test.WordUnreachDecoderDomain
open Flapjack Flapjack.Compiler.Backend.WordUnreach

def returningCall (width : Nat) : WordLangProgHOL (BitVec width) :=
  .call (some ([1], (.ln, .ln), .seq .skip (.move 0 [(5, 1)]), 2, 3))
    (some 7) [1] (some (9, .seq (.raise 9) .tick, 4, 5))

end Flapjack.Test.WordUnreachDecoderDomain

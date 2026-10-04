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

def returningExact (width : Nat) [NeZero width] : Bool :=
  match wordLangProgFromHOL (removeUnreach (returningCall width)) with
  | some (.call (some (values, sets, .move priority moves, firstLabel, secondLabel))
      target arguments (some (exception, .raise raised, handlerFirst, handlerSecond))) =>
      values == [1] && sets == ([], []) && priority == 0 && moves == [(5, 1)] &&
      firstLabel == 2 && secondLabel == 3 && target == some 7 && arguments == [1] &&
      exception == 9 && raised == 9 && handlerFirst == 4 && handlerSecond == 5
  | _ => false

-- Preserve every continuation field while transforming both nested bodies.
#guard returningExact 1
#guard returningExact 7
#guard returningExact 8
#guard returningExact 64
#guard returningExact 80

-- Inst Skip and FP have no executed carrier; a nonreturning Call retains its
-- handler literally in the original definition, including rejected leaves.
#guard (wordLangProgFromHOL (.inst .skip : WordLangProgHOL (BitVec 64))).isNone
#guard (wordLangProgFromHOL (removeUnreach
  (.call none (some 7) [] (some (9, .inst .skip, 4, 5)) : WordLangProgHOL (BitVec 64)))).isNone
#guard (wordLangProgFromHOL (removeUnreach
  (.seq (.inst .skip) .tick : WordLangProgHOL (BitVec 64)))).isNone

-- Domain preservation is one-way: a genuinely unreachable rejected tail may
-- disappear, while a rejected reachable instruction above stays rejected.
#guard (wordLangProgFromHOL (.seq (.return 0 []) (.inst .skip) :
  WordLangProgHOL (BitVec 64))).isNone
#guard match wordLangProgFromHOL (removeUnreach (.seq (.return 0 []) (.inst .skip) :
  WordLangProgHOL (BitVec 64))) with
  | some (.return label values) => label == 0 && values.isEmpty
  | _ => false

end Flapjack.Test.WordUnreachDecoderDomain

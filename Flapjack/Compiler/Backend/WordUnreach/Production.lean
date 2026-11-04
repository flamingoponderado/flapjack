import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.Compiler.Backend.WordUnreach.ProductionMemoryDomain
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip

/-!
# Executed unreachable-code removal through the reviewed `remove_unreach`

HOL `word_to_word$compile_single` (`word_to_wordScript.sml:31`) runs
`remove_unreach` after `three_to_two_reg_prog`. The executed allocator consumer
runs the tagged `WordUnreach.removeUnreach` (`Seq_assoc_right e Skip`, with
`SimpSeq` and `merge_moves`) at that point: the production program is encoded
with `wordLangProgToHOL`, the reviewed pass runs on the exact `wordLang$prog`
carrier, and the result is decoded with `wordLangProgFromHOL`. A program outside
the codec's domain is an explicit failure; no second implementation of the pass
is used. Flapjack production routing with no HOL declaration of its own.
-/

namespace Flapjack.RiscV

end Flapjack.RiscV

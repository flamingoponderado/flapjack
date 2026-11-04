import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
import Flapjack.Compiler.Backend.WordUnreach
import Flapjack.RiscV.CakeRegAlloc
import Flapjack.Compiler.Backend.WordCse.ListOrder
import Flapjack.Compiler.Backend.WordCse.RegisterUses
import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

/-!
# Executed word dead-code removal through reviewed `remove_dead_prog`

The executed allocator boundary runs HOL `remove_dead_prog`
(`word_allocScript.sml:1004-1006`, Flapjack `WordAlloc.removeDeadProg`) on the
exact `wordLang$prog` carrier: the production program is encoded with
`wordLangProgToHOL`, `removeDeadProg` runs, and the result is decoded with
`wordLangProgFromHOL`. A program the codec rejects (the executable-only
five-register AddCarry, or a nested use of it) keeps the historical executable
pass `wordRemoveDeadProgram`; this is the router's existing compatibility branch
for the broader Word extension, not a performance exception.
-/

namespace Flapjack.RiscV

end Flapjack.RiscV

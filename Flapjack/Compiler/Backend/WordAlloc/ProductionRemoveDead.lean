module

public import Flapjack.Compiler.Backend.WordAlloc.RemoveDead
public import Flapjack.Pancake.LoopToWord.WordProgCarrierCodec.RoundTrip
public import Flapjack.Compiler.Backend.WordUnreach
public import Flapjack.RiscV.CakeRegAlloc
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

@[expose] public section

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

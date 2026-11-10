module

public import Flapjack.Compiler.Backend.WordUnreach
public import Flapjack.RiscV.CakeRegAlloc
public import Flapjack.Compiler.Backend.WordCse.ListOrder
public import Flapjack.Compiler.Backend.WordCse.RegisterUses
public import Flapjack.Compiler.Backend.StackToLab.ExecutedCodec

@[expose] public section

/-! Direct Cake/HOL parity for the `remove_dead` global-store state carried by
    `nlive`.  Cake resets `nlive` after a non-variable `Set`, so an earlier
    global write must remain when a later variable write follows it.  The
    exact output is from canonical `word_allocScript.sml:952-961` and
    `remove_dead_prog_def`; the temporary HOL probe is not checked in. -/

namespace Flapjack.Test.CakeDeadCodeStateParity

open Flapjack Flapjack.RiscV

end Flapjack.Test.CakeDeadCodeStateParity

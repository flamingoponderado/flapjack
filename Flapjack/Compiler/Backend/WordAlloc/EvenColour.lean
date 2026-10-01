import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Misc.Sptree

namespace Flapjack.WordAlloc

/-- The original physical-register constraint on the actual sparse-tree entries.
Virtual keys impose no constraint; no well-formedness or domain premise is added. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "every_even_colour_def"]
def everyEvenColour (colour : Spt Nat) : Bool :=
  (sptToAList colour).all fun (key, value) =>
    if isPhyVar key then value == key / 2 else true

end Flapjack.WordAlloc

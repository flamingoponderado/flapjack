import Flapjack.Compiler.Backend.RegAlloc
import Flapjack.Misc.Sptree

namespace Flapjack.WordAlloc

/-- Literal total colouring lookup. Missing physical registers retain their
original key; other missing registers map to zero. Every mapped value is doubled. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "total_colour_def"]
def totalColour (colour : Spt Nat) (register : Nat) : Nat :=
  match sptLookup register colour with
  | none => if isPhyVar register then register else 0
  | some value => 2 * value

end Flapjack.WordAlloc

import Flapjack.Compiler.Backend.WordAlloc.Colour
import Flapjack.Compiler.Backend.WordAlloc.TotalColour
import Flapjack.Compiler.Backend.WordAlloc.EvenColour
import Flapjack.Compiler.Backend.RegAlloc.ClashTree
import Flapjack.Pancake.WordLang.OccurrencesExact

namespace Flapjack.WordAlloc

/-- Literal native oracle validator. All rejection branches remain explicit;
the checker accepts a colouring before applying it and checking stack bounds
and forced endpoint disequalities. Executed allocator migration is separate. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "oracle_colour_ok_def"
  (words_as_type_indexed_bitvec)]
def oracleColourOk {width : Nat} [NeZero width] (k : Nat)
    (colourOption : Option (Spt Nat)) (tree : RegAlloc.ClashTree)
    (program : WordLangProgHOL (BitVec width)) (forced : List (Nat × Nat)) :
    Option (WordLangProgHOL (BitVec width)) :=
  match colourOption with
  | none => none
  | some colour =>
      let tcol := totalColour colour
      if everyEvenColour colour && (RegAlloc.checkClashTree tcol tree .ln .ln).isSome then
        let coloured := applyColour tcol program
        if everyStackVarHOL (fun x => decide (2 * k ≤ x)) coloured &&
            forced.all (fun (x, y) => tcol x != tcol y) then
          some coloured
        else none
      else none

end Flapjack.WordAlloc

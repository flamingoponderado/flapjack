import Flapjack.Compiler.Backend.WordAlloc.HeuProg
import Flapjack.Compiler.Backend.WordAlloc.GetPrefs
import Flapjack.Compiler.Backend.WordAlloc.Heuristics
import Flapjack.Compiler.Backend.WordAlloc.CoalesceCost
import Flapjack.Compiler.Backend.WordAlloc.CanonizeMoves
import Flapjack.Misc.Sptree.Mapi

namespace Flapjack.WordAlloc

/-- Literal composition of the native heuristic collectors. Odd algorithms
collect counters and calls from two empty trees, use call absence for the
tail-cost multiplier, then weight canonicalized preferences. Even algorithms
return raw preferences and no spill-cost map. Production allocator routing
remains on the parent definition-composition bead. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "get_heuristics_def"
  (words_as_type_indexed_bitvec)]
def getHeuristics {width : Nat} [NeZero width] (algorithm functionName : Nat)
    (program : WordLangProgHOL (BitVec width)) :
    List (Nat × (Nat × Nat)) × Option (Spt Nat) :=
  if algorithm % 2 = 1 then
    let (tracked, calls) := getHeu functionName program (.ln, .ln)
    let moves := getPrefs program []
    let spillcosts := sptMapi (fun key value =>
      getSpillCost value (sptLookup key calls).isNone) tracked
    let canonMoves := canonizeMoves moves
    let heuMoves := canonMoves.map (getCoalesceCost spillcosts)
    (heuMoves, some spillcosts)
  else
    let moves := getPrefs program []
    (moves, none)

end Flapjack.WordAlloc

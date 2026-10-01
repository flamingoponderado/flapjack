import Flapjack.Pancake.WordLang
import Flapjack.PanToCrepMaxList

namespace Flapjack

/-- Literal maximum of both source Spt key enumerations, including trees
without a well-formedness premise. -/
@[hol "cakeml/compiler/backend/wordLangScript.sml" "cutsets_max_def"]
def cutsetsMaxHOL (cutsets : WordLangCutsetsHOL) : Nat :=
  max (maxList ((sptToAList cutsets.1).map Prod.fst))
    (maxList ((sptToAList cutsets.2).map Prod.fst))

end Flapjack

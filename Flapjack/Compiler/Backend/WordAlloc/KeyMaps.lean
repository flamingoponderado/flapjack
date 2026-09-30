import Flapjack.Misc.Sptree
import Flapjack.HolRef

namespace Flapjack.WordAlloc

/-- HOL key renaming retains payloads and rebuilds the exact numeric tree.
Colliding renamed keys retain the first association in HOL traversal order. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "apply_nummap_key_def"]
def applyNummapKey {α : Type} (f : Nat → Nat) (names : Spt α) : Spt α :=
  sptFromAList ((sptToAList names).map (fun (key, value) => (f key, value)))

end Flapjack.WordAlloc

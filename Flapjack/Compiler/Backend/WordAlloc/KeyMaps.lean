import Flapjack.Misc.Sptree
import Flapjack.HolRef

namespace Flapjack.WordAlloc

/-- HOL key renaming retains payloads and rebuilds the exact numeric tree.
Colliding renamed keys retain the first association in HOL traversal order. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "apply_nummap_key_def"]
def applyNummapKey {α : Type} (f : Nat → Nat) (names : Spt α) : Spt α :=
  sptFromAList ((sptToAList names).map (fun (key, value) => (f key, value)))

/-- Exact HOL paired key renaming. Both tree payload types are independent;
each component retains the original fromAList/map/toAList collision order. -/
@[hol "cakeml/compiler/backend/word_allocScript.sml" "apply_nummaps_key_def"]
def applyNummapsKey {α β : Type} (f : Nat → Nat) (names : Spt α × Spt β) : Spt α × Spt β :=
  (applyNummapKey f names.1, applyNummapKey f names.2)

end Flapjack.WordAlloc
